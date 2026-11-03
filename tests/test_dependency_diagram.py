"""Run graph behavior tests against the JavaScript embedded in offline pages."""
import shutil
import subprocess
import unittest
from pathlib import Path

from tools.rocq_readable.diagram import SCRIPT


class DiagramTests(unittest.TestCase):
    @unittest.skipUnless(shutil.which('node'), 'Node.js is required for browser-logic tests')
    def test_graph_behavior(self):
        harness = Path(__file__).with_name('dependency_diagram_checks.js').read_text()
        script = SCRIPT.removeprefix('<script>').removesuffix('</script>')
        script = script.replace('fixed.add(id);', 'fixed.add(id); checkFixed(fixed, points);')
        script = script.replace('  render();\n})();', '''  render();
  globalThis.graph = {importance, tiers, layout, render, zoom, fit, updateVisibility, popupPlacement,
    state: () => ({drawing, viewport, overviewWidth, currentTier}), mode, search};
})();''')
        result = subprocess.run(['node', '-e', harness], input=script, text=True, capture_output=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
