"""Fresh compiled programs must bypass expensive context-free CJR expansion."""
from contextlib import redirect_stderr
import io
from pathlib import Path
import unittest
from unittest.mock import patch

from tools.rocq_readable.cli import prepare
from tools.rocq_readable.project import Glob, Source


class CompiledRendering(unittest.TestCase):
    def run_prepare(self, fresh, valid_glob=True):
        root = Path('/tmp/readable-rendering-test')
        path = root / 'A.v'
        source = Source(path, root, '', 'P.A', Glob(valid=valid_glob))
        with patch('tools.rocq_readable.cli.Source.load', return_value=source), \
             patch('tools.rocq_readable.cli.Backend') as backend, \
             patch('tools.rocq_readable.cli.declarations'), \
             patch('tools.rocq_readable.semantics.classify_arrows'), \
             patch('tools.rocq_readable.gallina.fresh', return_value=fresh), \
             patch('tools.rocq_readable.gallina.render_source') as live, \
             patch('tools.rocq_readable.gallina.render_compiled') as contextual, \
             redirect_stderr(io.StringIO()):
            backend.return_value.__enter__.return_value.document.return_value = ({'spans': []}, [])
            sources, _ = prepare([path], root, 5)
            contextual.assert_called_once_with(sources, 5)
            return live.call_count

    def test_fresh_programs_print_once_with_shared_metadata(self):
        self.assertEqual(self.run_prepare(fresh=True), 0)

    def test_edited_or_uncompiled_sources_keep_the_live_printer(self):
        self.assertEqual(self.run_prepare(fresh=False), 1)

    def test_changed_resolution_context_keeps_the_live_printer(self):
        self.assertEqual(self.run_prepare(fresh=True, valid_glob=False), 1)
