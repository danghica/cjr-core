"""Correctness candidates use statements, while main status is reviewed metadata."""
import json
from pathlib import Path
import tempfile
import unittest

from tools.rocq_readable.ast import Declaration
from tools.rocq_readable.dependencies import build_graph
from tools.rocq_readable.html import diagram_data
from tools.rocq_readable.layout import Doc, Token
from tools.rocq_readable.project import Glob, Source


def reference(identity, offset):
    qid = {'v': ['Ser_Qualid', ['DirPath', []], ['Id', identity.rsplit('.', 1)[-1]]], 'loc': {'bp': offset, 'ep': offset+1}}
    return {'v': ['CRef', qid, None]}


def wp(operation, representation):
    return {'v': ['CNotation', None, ['InConstrEntry', 'WP _ {{ _ , _ } }'],
                  [[reference(operation, 10), {'v': ['CHole']}, reference(representation, 20)], [], [], []]]}


class CorrectnessContracts(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.sources, self.documents = [], {}
        self.model = self.add('spec/model.v', 'P.spec.model.contents', 'definition')
        self.operation = self.add('algorithm/program.v', 'P.algorithm.program.insert', 'definition')
        self.representation = self.add('proof/ownership.v', 'P.proof.ownership.tree_rep', 'definition', [self.model.identity], representation=True)
        self.contract = self.add('proof/main.v', 'P.proof.main.correct', 'theorem', [self.operation.identity, self.representation.identity])
        self.contract.type = wp(self.operation.identity, self.representation.identity)
        self.configure([self.contract.identity])

    def configure(self, main):
        (self.root / 'project.config.json').write_text(json.dumps({'main_correctness_contracts': main}))

    def add(self, file, identity, kind, refs=(), representation=False):
        text = ('iProp' if representation else '') + ' '*150
        source = Source(self.root/file, self.root, text, identity.rsplit('.', 1)[0], Glob(valid=True))
        decl = Declaration(identity.rsplit('.', 1)[-1], identity, kind, {}, text[:100],
                           body={'v': ['CPrim']} if kind == 'definition' else None,
                           type={'v': ['CPrim'], 'loc': {'bp': 0, 'ep': 5}} if representation else None,
                           proof_complete=True if kind == 'theorem' else None)
        source.declarations = [decl]
        for offset, ref in zip([10, 20], refs):
            source.glob.references[offset] = (offset+1, ref, 'def')
        self.sources.append(source)
        self.documents[source.path] = [Doc(Token(decl.name, anchor='own'), [Doc(Token(ref, identity=ref)) for ref in refs], block=True)]
        return decl

    def graph(self):
        return build_graph(self.sources, self.documents, {})

    def test_confirmed_bridge_embeds_operations_spec_and_representation(self):
        graph = self.graph()
        record = graph.contracts[self.contract.identity]
        self.assertTrue(record['main'])
        self.assertEqual(record['operations'], [self.operation.identity])
        self.assertEqual(record['specifications'], [self.model.identity])
        self.assertEqual(record['representations'], [self.representation.identity])
        self.assertEqual(set(record['related']), {self.operation.identity, self.model.identity, self.representation.identity})
        symbols = {d.identity: (self.root/'out.html', 'entry-'+d.name) for s in self.sources for d in s.declarations}
        text = diagram_data(self.sources, self.root/'out.html', symbols, graph)
        nodes = json.loads(text.split('>', 1)[1].rsplit('</script>', 1)[0])
        self.assertTrue(nodes[self.contract.identity]['main_contract'])
        self.assertFalse(nodes[self.operation.identity]['main_contract'])
        self.assertEqual(nodes[self.contract.identity]['statement_dependencies'], sorted([self.operation.identity, self.representation.identity]))

    def test_unreviewed_candidates_do_not_receive_main_status(self):
        self.configure([])
        record = self.graph().contracts[self.contract.identity]
        self.assertFalse(record['main'])
        self.assertEqual(record['selection'], 'detected candidate')

    def test_proof_references_do_not_turn_a_pure_statement_into_a_contract(self):
        self.contract.type = {'v': ['CPrim']}
        self.contract.proof_spans = [wp(self.operation.identity, self.representation.identity)]
        self.assertNotIn(self.contract.identity, self.graph().contracts)

    def test_internal_body_references_are_not_public_operation_calls(self):
        self.contract.type['v'][3][0][0] = {'v': ['CApp', reference('cjr.lang.App', 30), [[reference(self.operation.identity, 10), None]]]}
        self.assertNotIn(self.contract.identity, self.graph().contracts)

    def test_specification_in_a_binder_does_not_replace_a_postcondition_bridge(self):
        self.contract.type['v'][3][0][-1] = {'v': ['CPrim']}
        self.assertNotIn(self.contract.identity, self.graph().contracts)

    def test_proof_edges_remain_available_but_outside_statement_edges(self):
        self.contract.type = {'v': ['CPrim']}
        self.contract.proof_spans = [{'v': ['CPrim'], 'loc': {'bp': 100, 'ep': 121}}]
        source = self.sources[-1]
        source.glob.references = {110: (111, self.model.identity, 'def')}
        self.documents[source.path] = [Doc(Token(self.contract.name, anchor='own'))]
        graph = self.graph()
        self.assertEqual(graph.edges[self.contract.identity], [self.model.identity])
        self.assertEqual(graph.statement_edges[self.contract.identity], [])

    def test_aborted_proof_is_not_promoted_by_an_annotation(self):
        self.contract.proof_complete = False
        self.assertNotIn(self.contract.identity, self.graph().contracts)

    def test_local_homonyms_cannot_become_operations(self):
        source = self.sources[-1]
        source.glob.valid = False
        self.contract.binders = [{'v': ['Name', ['Id', 'insert']]}]
        self.assertNotIn(self.contract.identity, self.graph().contracts)

    def test_bad_configuration_is_reported(self):
        self.configure('not a list')
        with self.assertRaisesRegex(ValueError, 'main_correctness_contracts'):
            self.graph()

    def test_explicit_specification_module_without_spec_directory(self):
        source = self.sources[0]
        source.path = self.root/'core/model.v'
        self.documents[source.path] = self.documents.pop(self.root/'spec/model.v')
        self.assertNotIn(self.contract.identity, self.graph().contracts)
        (self.root/'project.config.json').write_text(json.dumps({
            'correctness_specification_modules': [source.module],
            'main_correctness_contracts': [self.contract.identity]}))
        self.assertTrue(self.graph().contracts[self.contract.identity]['main'])

    def test_reviewed_call_wrapper_uses_the_body_as_operation(self):
        wrapper = self.add('algorithm/calls.v', 'P.algorithm.calls.call', 'definition')
        source = self.sources[-2]
        source.glob.references[30] = (31, wrapper.identity, 'def')
        self.documents[source.path][0].children.append(Doc(Token(wrapper.name, identity=wrapper.identity)))
        self.contract.type['v'][3][0][0] = {
            'v': ['CApp', reference(wrapper.identity, 30),
                  [[reference(self.operation.identity, 10), None]]]}
        self.assertEqual(self.graph().contracts[self.contract.identity]['operations'], [wrapper.identity])
        (self.root/'project.config.json').write_text(json.dumps({
            'correctness_call_wrappers': [wrapper.identity]}))
        self.assertEqual(self.graph().contracts[self.contract.identity]['operations'], [self.operation.identity])

    def test_invalid_role_configuration_is_reported(self):
        for key in ['correctness_specification_modules', 'correctness_call_wrappers']:
            with self.subTest(key=key):
                (self.root/'project.config.json').write_text(json.dumps({key: 'not a list'}))
                with self.assertRaisesRegex(ValueError, key):
                    self.graph()
