import json,os,subprocess,tempfile,unittest
from pathlib import Path
from unittest.mock import patch
from tools.project_tools.workspace import dependencies,main
from tools.project_tools.link_audit import audit

class WorkspaceTests(unittest.TestCase):
    def test_missing_dependency_has_actionable_override(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp)/'consumer';root.mkdir()
            (root/'dependencies.lock.json').write_text('{"cjr-core":"abc"}')
            with patch.dict(os.environ,{'CJR_CORE_DIR':str(Path(tmp)/'missing')}):
                with self.assertRaisesRegex(RuntimeError,'CJR_CORE_DIR'):dependencies(root)

    def test_version_mismatch_rejected_and_override_resolved(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp)/'consumer';root.mkdir()
            core=Path(tmp)/'custom-core';core.mkdir();(core/'repository.json').write_text('{}')
            (root/'dependencies.lock.json').write_text('{"cjr-core":"expected"}')
            with patch.dict(os.environ,{'CJR_CORE_DIR':str(core)}),patch('subprocess.check_output',return_value='other\n'):
                with self.assertRaisesRegex(RuntimeError,'version mismatch'):dependencies(root)
            with patch.dict(os.environ,{'CJR_CORE_DIR':str(core)}),patch('subprocess.check_output',return_value='expected\n'):
                self.assertEqual(dependencies(root)['cjr-core'],core.resolve())

    def test_docs_command_never_invokes_proof_build_or_renderer(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);(root/'docs').mkdir();(root/'dependencies.lock.json').write_text('{}');(root/'repository.json').write_text('{"examples":[]}')
            with patch('sys.argv',['project.py','docs']),patch('tools.project_tools.workspace.proof_build') as proofs,patch('tools.project_tools.workspace.pages') as pages:
                with patch.dict(os.environ):
                    main(root)
                proofs.assert_not_called();pages.assert_called_once_with(root)

    def test_offline_audit_checks_files_and_fragments(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);(root/'index.html').write_text('<a href="other.html#ok">valid</a>')
            (root/'other.html').write_text('<h1 id="ok">Other</h1>')
            self.assertEqual(audit(root)['status'],'passed')
            (root/'other.html').write_text('<h1>Other</h1>')
            self.assertEqual(audit(root)['errors'][0]['reason'],'missing fragment')

    def test_core_printer_and_framework_do_not_import_collections(self):
        root=Path(__file__).resolve().parents[1]
        owned={p.stem for folder in ['theories','tools/extraction/rocq','example'] for p in (root/folder).rglob('*.v')}
        import re
        for folder in ['theories','tools/extraction/rocq']:
            for source in (root/folder).glob('*.v'):
                for group in re.findall(r'From cjr\.examples Require(?: Import| Export)?\s+([\w\s]+)\.',source.read_text()):
                    for module in group.split():self.assertIn(module,owned,str(source)+': '+module)
