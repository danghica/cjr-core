"""Native compiler checks for annotations the structural checker cannot typecheck.

Run after building the generic Rocq modules. These regressions ensure that a
receiver annotation cannot silently select a different native field layout.
"""
import re
import subprocess
import tempfile
import unittest
from pathlib import Path

from tools.project_tools.examples import ROOT, coq_flags
from tools.project_tools.support import toolchain


class GenericExtractionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.compiler, cls.env, _ = toolchain(ROOT)

    def extract_source(self, declarations):
        query = ('From Coq Require Import String List.\n'
                 'From cjr Require Import generics.\n'
                 'From cjr.examples Require Import generic_print generic_examples.\n'
                 'Import ListNotations.\nOpen Scope string_scope.\n' + declarations +
                 '\nEval vm_compute in generic_source bad_program.\n')
        result = subprocess.run(
            [str(Path.home() / '.opam/default/bin/coqtop'), '-quiet', *coq_flags()],
            input=query, text=True, capture_output=True, cwd=ROOT, check=True)
        self.assertNotIn('Error:', result.stderr, result.stderr)
        match = re.search(r'=\s*"(.*)"(?:%string)?\s*:\s*string', result.stdout, re.S)
        self.assertIsNotNone(match, result.stdout)
        source = match.group(1).replace('""', '"')
        self.assertNotIn('unsupported', source, source)
        return source

    def compile_source(self, declarations):
        source = self.extract_source(declarations)
        with tempfile.TemporaryDirectory(prefix='cjr-generic-rejection-') as directory:
            path = Path(directory) / 'program.cj'
            path.write_text(source)
            compiled = subprocess.run([str(self.compiler), str(path), '-o', str(Path(directory) / 'program')],
                                      env=self.env, text=True, capture_output=True)
        self.assertNotEqual(compiled.returncode, 0, source)
        self.assertIn('error', compiled.stderr.lower(), compiled.stderr)
        self.assertTrue('type' in compiled.stderr.lower() or 'match' in compiled.stderr.lower(), compiled.stderr)

    def test_reordered_fields_cannot_use_an_unrelated_receiver_annotation(self):
        self.compile_source('''
Definition swapped := GLayout "Swapped" GStruct [] [("second", GTBool); ("first", GTInt)].
Definition bad_program := GProgram (pair_layout :: swapped :: []) []
  (GEField (pair_ty GTInt GTBool)
    (GEConstruct (GTNamed "Swapped" []) [GEVal (LitV (LitBool true)); GEVal (LitV (LitInt 7))]) 0).
''')

    def test_method_receiver_type_arguments_are_checked(self):
        self.compile_source('''
Definition bad_program := GProgram generic_layouts generic_functions
  (GEMethod (box_ty GTBool) (GEConstruct (box_ty GTInt) [GEVal (LitV (LitInt 7))]) "get" [] []).
''')

    def test_lambda_result_annotation_is_checked(self):
        self.compile_source('''
Definition bad_program := GProgram [] []
  (GEApp (GELam "x" GTInt GTBool (GEVar "x")) (GEVal (LitV (LitInt 7)))).
''')

    def test_buffer_receiver_annotation_is_checked(self):
        self.compile_source('''
Definition bad_program := GProgram [] []
  (GEBufferGet GTBool
    (GEBufferMake GTInt (GEVal (LitV (LitInt 2))) (GEVal (LitV (LitInt 7))))
    (GEVal (LitV (LitInt 0)))).
''')

    def test_buffer_write_type_is_checked(self):
        self.compile_source('''
Definition bad_program := GProgram [] []
  (GEBufferSet GTInt
    (GEBufferMake GTInt (GEVal (LitV (LitInt 2))) (GEVal (LitV (LitInt 0))))
    (GEVal (LitV (LitInt 0))) (GEVal (LitV (LitBool true)))).
''')

    def test_buffer_operands_evaluate_once_in_order(self):
        source = self.extract_source('''
Definition zero := GEVal (LitV (LitInt 0)).
Definition one := GEVal (LitV (LitInt 1)).
Definition note digit result := GELet None
  (GEBufferSet GTInt (GEVar "trace") zero
    (GEBinOp PlusOp
      (GEBinOp MulOp (GEBufferGet GTInt (GEVar "trace") zero) (GEVal (LitV (LitInt 10))))
      (GEVal (LitV (LitInt digit))))) result.
Definition order_fn := GFunction "bufferOrder" None [] [] GTInt
  (GELet (Some "trace") (GEBufferMake GTInt one zero)
   (GELet (Some "target") (GEBufferMake GTInt (note 1 one) (note 2 zero))
    (GELet None
      (GEBufferSet GTInt (note 3 (GEVar "target")) (note 4 zero) (note 5 one))
      (GELet None
        (GEBufferGet GTInt (note 6 (GEVar "target")) (note 7 zero))
        (GEBufferGet GTInt (GEVar "trace") zero))))).
Definition bad_program := GProgram [] [order_fn] (GEVal (LitV LitUnit)).
''')
        with tempfile.TemporaryDirectory(prefix='cjr-buffer-order-') as directory:
            path = Path(directory) / 'program.cj'
            path.write_text(source)
            test = Path(directory) / 'order_test.cj'
            test.write_text('''@Test
class BufferOrderTests {
    @TestCase func operands(): Unit { @Expect(bufferOrder(), 1234567) }
}
''')
            binary = Path(directory) / 'order'
            compiled = subprocess.run(
                [str(self.compiler), '--test', '-O2', str(path), str(test), '-o', str(binary)],
                env=self.env, text=True, capture_output=True)
            self.assertEqual(compiled.returncode, 0, compiled.stderr)
            ran = subprocess.run([str(binary), '--no-progress', '--no-color'],
                                 env=self.env, text=True, capture_output=True)
            self.assertEqual(ran.returncode, 0, ran.stdout + ran.stderr)
            self.assertRegex(ran.stdout, r'\[\s*PASSED\s*\]\s+CASE:\s+operands')

    def test_static_method_scope_and_argument_order(self):
        source = self.extract_source('''
Definition zero := GEVal (LitV (LitInt 0)).
Definition note digit result := GELet None
  (GEBufferSet GTInt (GEVar "trace") zero
    (GEBinOp PlusOp
      (GEBinOp MulOp (GEBufferGet GTInt (GEVar "trace") zero) (GEVal (LitV (LitInt 10))))
      (GEVal (LitV (LitInt digit))))) result.
Definition choose_fn := GStaticFunction "choose" "Box" ["U"]
  [("left", tT); ("right", tU)] tU (GEVar "right").
Definition order_fn := GFunction "staticOrder" None [] [] GTInt
  (GELet (Some "trace") (GEBufferMake GTInt (GEVal (LitV (LitInt 1))) zero)
    (GELet None
      (GEStaticCall (box_ty GTInt) "choose" [GTBool]
        [note 1 (GEVal (LitV (LitInt 7))); note 2 (GEVal (LitV (LitBool true)))])
      (GEBufferGet GTInt (GEVar "trace") zero))).
Definition bad_program := GProgram [box_layout] [choose_fn; order_fn] (GEVal (LitV LitUnit)).
''')
        with tempfile.TemporaryDirectory(prefix='cjr-static-method-') as directory:
            path = Path(directory) / 'program.cj'
            path.write_text(source)
            test = Path(directory) / 'static_test.cj'
            test.write_text('''@Test
class StaticMethodTests {
    @TestCase func staticScopeAndOrder(): Unit {
        @Expect(Box<Int64>.choose<Bool>(7, true), true)
        @Expect(staticOrder(), 12)
    }
}
''')
            binary = Path(directory) / 'static'
            compiled = subprocess.run(
                [str(self.compiler), '--test', '-O2', str(path), str(test), '-o', str(binary)],
                env=self.env, text=True, capture_output=True)
            self.assertEqual(compiled.returncode, 0, compiled.stderr)
            ran = subprocess.run([str(binary), '--no-progress', '--no-color'],
                                 env=self.env, text=True, capture_output=True)
            self.assertEqual(ran.returncode, 0, ran.stdout + ran.stderr)
            self.assertRegex(ran.stdout, r'\[\s*PASSED\s*\]\s+CASE:\s+staticScopeAndOrder')


if __name__ == '__main__':
    unittest.main()
