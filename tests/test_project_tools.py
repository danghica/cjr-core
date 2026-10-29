import tempfile
import unittest
import csv
import json
import sys
from pathlib import Path

from tools.project_tools.benchmark import normalize, provenance_root
from tools.project_tools.docs import HTMLInfo, check_links
from tools.project_tools.docs import hashes
from tools.project_tools.benchmark import load_config, render, plot
from tools.project_tools.examples import PROGRAMS, ROOT, code_path
from tools.rocq_readable.project import configuration, module_name


class ProjectToolTests(unittest.TestCase):
    def test_custom_benchmark_plot_command_receives_resolved_paths(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp)
            output=root/'results'; output.mkdir()
            (output/'summary.json').write_text('[]')
            script=root/'plot.py'
            script.write_text('import sys; from pathlib import Path; '
                              'Path(sys.argv[1], "marker").write_text(sys.argv[2])')
            config=root/'benchmark.json'
            config.write_text(json.dumps({'output':'results', 'plots':{'command':
                [sys.executable, '{root}/plot.py', '{output}', '{root}']}}))
            plot(config)
            self.assertEqual((output/'marker').read_text(),str(root.resolve()))

    def test_benchmark_dots_encode_measured_time_on_shared_axis(self):
        import xml.etree.ElementTree as ET
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            output = root / 'results'; output.mkdir()
            records = [dict(case='build', n=256, implementation=impl,
                            median_ns=median, q1_ns=median-1, q3_ns=median+2)
                       for impl, median in [('CJR', 30), ('Std', 15)]]
            (output / 'summary.json').write_text(json.dumps(records))
            config = root / 'benchmark.json'
            config.write_text(json.dumps({'output': 'results', 'plots': {'facet': 'case'}}))
            plot(config)
            svg = ET.parse(output / 'build.svg')
            ns = {'s': 'http://www.w3.org/2000/svg'}
            dots = svg.findall('.//s:g/s:circle', ns)
            self.assertEqual(len(dots), 2)
            xs = [float(dot.attrib['cx']) for dot in dots]
            self.assertGreater(xs[0], xs[1])
            self.assertAlmostEqual((xs[0]-230)/(xs[1]-230), 2, places=3)
            for group, record in zip(svg.findall('.//s:g', ns), records):
                path = group.find('s:path', ns).attrib['d'].split()
                self.assertAlmostEqual(float(path[1]), 230+650*record['q1_ns']/32, places=1)
                self.assertAlmostEqual(float(path[-1]), 230+650*record['q3_ns']/32, places=1)

    def test_native_benchmark_source_is_in_provenance(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp)
            source=root/'benchmark.c'; source.write_text('int main(void) { return 0; }')
            before=hashes(root)
            self.assertIn('benchmark.c',before)
            source.write_text('int main(void) { return 1; }')
            self.assertNotEqual(before['benchmark.c'],hashes(root)['benchmark.c'])

    def test_benchmark_provenance_can_scope_a_nested_report(self):
        self.assertEqual(provenance_root({}, ROOT), ROOT)
        self.assertEqual(provenance_root({'provenance_root': 'example/aes_ige'}, ROOT),
                         ROOT / 'example/aes_ige')
        with self.assertRaises(ValueError):
            provenance_root({'provenance_root': '..'}, ROOT)

    def test_report_inventory_reads_rendered_declaration_articles(self):
        page = HTMLInfo('<nav aria-label="Project"><a href="index.html">Home</a></nav>'
                        '<article id="symbol-a"><h2>array_cells</h2><p>description</p></article>'
                        '<article id="symbol-b"><h2>array_get</h2></article>')
        self.assertEqual(page.declarations, [("#symbol-a", "array_cells"), ("#symbol-b", "array_get")])

    def test_relocated_examples_preserve_logical_names_and_compile_inputs(self):
        for line in (ROOT / '_CoqProject').read_text().splitlines():
            if not line.endswith('.v'):
                continue
            path = ROOT / line
            self.assertTrue(path.is_file(), line)
            identity = module_name(path, configuration(path, ROOT), ROOT)
            if line.startswith('example/aes_ige/rocq/'):
                self.assertEqual(identity, 'cjr.aes_ige.' + path.stem)
            elif line.startswith('example/authenticator/core/rocq/'):
                self.assertEqual(identity, 'cjr.authenticator.' + path.stem)
            elif '/rocq/' in line:
                self.assertEqual(identity, 'cjr.examples.' + path.stem)
            elif line.startswith('example/quadtree/'):
                self.assertEqual(identity, 'cjr.quadtree.' + '.'.join(path.relative_to(ROOT / 'example/quadtree').with_suffix('').parts))
        for program in PROGRAMS:
            self.assertTrue(code_path(program).is_file(), program)
            self.assertTrue((code_path(program).parents[1] / 'test' / (program + '_test.cj')).is_file())
        for config in (ROOT / 'example').glob('*/benchmark/benchmark.config.json'):
            data, root = load_config(config)
            for job in data['jobs']:
                for relative in [*job['sources'], *job.get('harness_sources', [])]:
                    self.assertTrue((root / relative).is_file(), str(config) + ': ' + relative)
                    self.assertTrue((root / relative).resolve().is_relative_to(ROOT))
                command = render(job['compile'], {'root': root, 'cjc': 'cjc', 'binary': '/tmp/test-binary'})
                for arg in command:
                    if arg.endswith('.cj'):
                        self.assertTrue(Path(arg).is_file(), arg)

    def test_historical_benchmark_partitions_preserve_provenance_until_rerun(self):
        historical = ROOT / 'paper/benchmark-history'
        with (historical / 'raw.csv').open() as stream:
            original = list(csv.DictReader(stream))
        original_metadata = json.loads((historical / 'metadata.json').read_text())
        key = lambda row: tuple(sorted(row.items()))
        for name, prefix in [('list', 'list_'), ('array', 'array_'),
                             ('array_list', 'arraylist_'), ('hash_map', 'hashmap_')]:
            output = ROOT / 'example' / name / 'benchmark/results'
            with (output / 'raw.csv').open() as stream:
                partition = list(csv.DictReader(stream))
            data = json.loads((output / 'metadata.json').read_text())
            self.assertEqual(data['samples'], len(partition))
            if data.get('historical'):
                self.assertEqual(data['date_utc'], original_metadata['date_utc'])
                self.assertEqual(data['sources'], original_metadata['sources'])
                expected = [row for row in original if row['case'].startswith(prefix)]
                self.assertCountEqual([key(row) for row in partition], [key(row) for row in expected])
            else:
                self.assertGreater(data['date_utc'], original_metadata['date_utc'])
                self.assertTrue(data['benchmark_sources'])
                self.assertTrue(data['harness_sources'])

    def test_saved_report_requires_opt_in_and_preserves_failed_check_rejection(self):
        from tools.project_tools.docs import report
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / 'style.css').write_text('')
            saved = root / 'tests.json'
            data = {'sources': {'program.cj': 'previous-hash'},
                    'status': 'passed', 'date_utc': '2026-10-12T00:00:00Z'}
            saved.write_text(json.dumps(data))
            before = saved.read_bytes()
            config = root / 'project.config.json'
            config.write_text(json.dumps({'css': 'style.css', 'artifacts': {'tests': 'tests.json'}}))
            with self.assertRaisesRegex(RuntimeError, 'Stale tests'):
                report(config)
            report(config, allow_stale=True)
            page = (root / 'index.html').read_text()
            self.assertIn('Saved results from earlier source snapshots', page)
            self.assertIn(data['date_utc'], page)
            self.assertEqual(saved.read_bytes(), before)
            data['status'] = 'failed'; saved.write_text(json.dumps(data))
            with self.assertRaisesRegex(RuntimeError, 'has not passed'):
                report(config, allow_stale=True)

    def test_nested_example_provenance_tracks_shared_and_sibling_sources(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            for relative in ('theories/lang.v', 'tools/project_tools/docs.py',
                             'tools/extraction/rocq/cj_print.v', 'example/array/rocq/array.v'):
                path = root / relative; path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text('initial')
            project = root / 'example/quadtree'; project.mkdir()
            before = hashes(project)
            shared = root / 'tools/extraction/rocq/cj_print.v'
            shared.write_text('changed')
            after = hashes(project)
            self.assertIn('../array/rocq/array.v', before)
            self.assertNotEqual(before['../../tools/extraction/rocq/cj_print.v'],
                                after['../../tools/extraction/rocq/cj_print.v'])

    def test_benchmark_rows_preserve_dimensions_and_normalize_time(self):
        row = normalize(
            {"name": "range", "dimensions": {"distribution": "uniform"}},
            {"n": "256", "workload": "selective", "implementation": "CJR",
             "trial": "2", "repetitions": "4", "elapsed_ns": "800", "checksum": "11"},
            1,
        )
        self.assertEqual(row["distribution"], "uniform")
        self.assertEqual(row["n"], 256)
        self.assertEqual(row["checksum"], 11)
        self.assertEqual(row["process"], 1)
        self.assertEqual(row["ns_per_operation"], 200)

    def test_link_checker_accepts_local_destination_and_fragment(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / "index.html").write_text('<a href="child.html#decl">child</a>')
            (root / "child.html").write_text('<h1 id="decl">declaration</h1>')
            check_links(root)

    def test_link_checker_rejects_links_outside_project(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / "index.html").write_text('<a href="../outside.html">outside</a>')
            with self.assertRaisesRegex(RuntimeError, "leaves project"):
                check_links(root)

    def test_link_checker_rejects_missing_fragment(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / "index.html").write_text('<a href="child.html#missing">child</a>')
            (root / "child.html").write_text('<h1 id="present">declaration</h1>')
            with self.assertRaisesRegex(RuntimeError, "missing local anchor"):
                check_links(root)


if __name__ == "__main__":
    unittest.main()
