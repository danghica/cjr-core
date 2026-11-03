"""The HTML Cangjie view must be the actual Gallina printer's output."""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

from tools.rocq_readable.cli import DEFAULT_DICTIONARY, generate, prepare
from tools.rocq_readable.backend import BackendError, executable
from tools.rocq_readable.dictionary import Dictionary
from tools.rocq_readable.gallina import fresh, result_text
from tools.rocq_readable.project import Source

ROOT = Path(__file__).resolve().parents[1]


def backend_available():
    if os.environ.get('CJR_SKIP_PROOF_BACKEND') == '1':
        return False
    try:
        executable()
    except BackendError:
        return False
    return (ROOT / 'tools/extraction/rocq/cj_print.vo').is_file()


class PrinterResponses(unittest.TestCase):
    def test_only_completed_string_results_are_displayed(self):
        self.assertEqual(result_text({'feedback': [[4, '"a ""quoted""\nline"']]}),
                         {'status': 'available', 'text': 'a "quoted"\nline'})
        self.assertIsNone(result_text({'feedback': [[4, '(ex env body)']]}))
        self.assertIsNone(result_text({'feedback': [[4, 'CJR-NONE']]}))
        self.assertEqual(result_text({'feedback': [[4, '"/* unsupported: stack form */"']]})['status'], 'unavailable')


@unittest.skipUnless(backend_available(), 'build the Gallina printer and install coq-lsp for integration tests')
class GallinaPrinterIntegration(unittest.TestCase):
    def test_uncompiled_definitions_helpers_and_html(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / '_CoqProject').write_text(f'-R {ROOT / "theories"} cjr\n-Q {ROOT / "tools/extraction/rocq"} cjr.examples\n-Q . PrinterTest\n')
            path = root / 'A.v'
            path.write_text('''From Coq Require Import String List.
From cjr Require Import lang.
From cjr.examples Require Import cj_print.
Open Scope string_scope.
Definition number := Val (LitV (LitInt 7)).
Definition plus a b := BinOp PlusOp a b.
Definition escaped := Var "<tag>&".
Definition ordinary := 3.
Definition integer_argument n := Val (LitV (LitInt n)).
Definition stack := StackLoad (Var "stack").
Definition point := Decl "Point" (("x", "Int64") :: nil).
Definition program := Prog (point :: nil) nil nil number.
''')
            sources, resolutions = prepare([path], root, 60)
            source = sources[0]
            self.assertEqual(source.errors, [])
            records = source.cangjie
            self.assertEqual(records['PrinterTest.A.number']['text'], '7')
            self.assertEqual(records['PrinterTest.A.plus']['text'], 'a + b')
            self.assertNotIn('PrinterTest.A.ordinary', records)
            self.assertEqual(records['PrinterTest.A.integer_argument']['status'], 'unavailable')
            self.assertEqual(records['PrinterTest.A.stack']['status'], 'unavailable')
            self.assertIn('class Point', records['PrinterTest.A.program']['text'])
            output = root / 'html'
            generate(sources, resolutions, Dictionary(DEFAULT_DICTIONARY), output)
            text = (output / 'A.html').read_text()
            self.assertIn('Cangjie · Gallina printer', text)
            self.assertIn('&lt;tag&gt;&amp;', text)
            self.assertIn('Original declaration (proof-free)', text)
            self.assertIn('Rocq structure', text)
            self.assertFalse(fresh(source))
            # A fresh compiled module allows program signatures/layouts to be
            # shared with expression definitions and printed as full functions.
            path.write_text(path.read_text().replace('nil nil number.',
                'nil ((Fn "seven" None None number nil "Int64") :: nil) number.'))
            result = subprocess.run([str(Path.home()/'.opam/default/bin/coqc'),
                '-R', str(ROOT/'theories'), 'cjr', '-Q', str(ROOT/'tools/extraction/rocq'), 'cjr.examples',
                '-Q', '.', 'PrinterTest', 'A.v'], cwd=root, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            sources, _ = prepare([path], root, 60)
            self.assertTrue(fresh(sources[0]))
            self.assertIn('func seven(): Int64', sources[0].cangjie['PrinterTest.A.number']['text'])
            path.write_text(path.read_text() + '\n(* source edited since compilation *)\n')
            self.assertFalse(fresh(Source.load(path, root)))
