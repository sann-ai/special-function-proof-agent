"""Definition-preserving proofs, research composition, and fixed AI authority."""
from copy import deepcopy
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from special_function_agent import defined_proof, research_functions as functions
from special_function_agent import research_library
from special_function_agent.archive import target_hash
from special_function_agent.core import InputError, replay, validate_request, verify
from special_function_agent.generate import make_prompt, output_schema
from special_function_agent.parser import parse_identity
from special_function_agent.research_generation import attach_lemmas


def variable(name): return {'op': 'var', 'name': name}
def integer(value): return {'op': 'int', 'value': value}
def binary(op, left, right): return {'op': op, 'args': [left, right]}
def definition(body=None, name='ShiftedGamma', dependencies=None):
    return functions.make_definition({'schema_version': 1, 'name': name,
        'parameters': {'u': 'real'}, 'body': body or {'op': 'gamma', 'arg': binary('add', variable('u'), integer(1))},
        'definitions': dependencies or []})
def call(snapshot, arg): return {'op': 'defined', 'function': snapshot['id'], 'arguments': {'u': arg}}
def source_target(snapshot=None):
    snapshot = snapshot or definition()
    target = parse_identity('Gamma(x+1)=x*Gamma(x);x>0')
    target.update(lhs=call(snapshot, variable('x')), definitions=[snapshot])
    return target


class DefinedInputIntegrationTests(unittest.TestCase):
    def test_definition_identity_changes_without_changing_old_target_hashes(self):
        target = source_target()
        changed = source_target(definition(binary('add', variable('u'), integer(1))))
        self.assertNotEqual(target_hash(target), target_hash(changed))
        self.assertNotEqual(target_hash(target), target_hash(functions.expand_target(target)))
        self.assertEqual(target_hash(target), target_hash({**target, 'proof': defined_proof.default_proof(target)}))

    def test_model_schema_selects_existing_definitions_only(self):
        target = source_target()
        schema = output_schema('steps', target)
        calls = [node for node in schema['$defs']['expr']['anyOf']
                 if node['properties'].get('op', {}).get('const') == 'defined']
        self.assertEqual(len(calls), 1)
        self.assertEqual(calls[0]['properties']['function']['const'], target['definitions'][0]['id'])
        self.assertEqual(set(schema['properties']), {'mode', 'steps'})
        self.assertIn('Expanded target', make_prompt(target, 'steps'))
        from special_function_agent.real_bessel import _walk
        self.assertTrue(all('type' in node for node in _walk(schema) if 'const' in node))

    def test_candidate_cannot_replace_definitions_target_or_assumptions(self):
        target = source_target()
        for field, value in [('definitions', []), ('target', target), ('assumptions', []), ('lean', 'axiom bad : False')]:
            with self.subTest(field=field), self.assertRaises(InputError):
                validate_request({**target, 'proof': {**defined_proof.default_proof(target), field: value}})

    def test_original_step_endpoint_is_checked_before_expansion(self):
        target = source_target()
        proof = defined_proof.default_proof(target, 'steps')
        proof['steps'][0]['before'] = functions.expand_target(target)['lhs']
        with self.assertRaises(InputError):
            validate_request({**target, 'proof': proof})


@unittest.skipUnless(os.environ.get('SF_RUN_LEAN_TESTS') == '1', 'Set SF_RUN_LEAN_TESTS=1 for real Lean integration.')
class DefinedLeanIntegrationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temporary = tempfile.TemporaryDirectory(prefix='sf-defined-tests-')
        cls.root = Path(cls.temporary.name)
        cls.target = source_target()
        cls.source = cls.root/'source'
        result = verify({**cls.target, 'proof': defined_proof.default_proof(cls.target)}, cls.source)
        if result.get('status') != 'proved':
            raise AssertionError(result)
        cls.package = research_library.register(cls.source, cls.root/'research', name='shifted-gamma-step')

    @classmethod
    def tearDownClass(cls): cls.temporary.cleanup()

    def location(self): return Path(tempfile.mkdtemp(dir=self.root))/'run'

    def test_direct_and_steps_keep_original_calls_and_expanded_theorem(self):
        for route in ['direct', 'steps']:
            output = self.location()
            result = verify({**self.target, 'proof': defined_proof.default_proof(self.target, route)}, output)
            self.assertEqual(result['status'], 'proved', result)
            source = (output/'certificate.lean').read_text()
            self.assertIn('theorem expanded_target', source)
            self.assertIn('theorem target', source)
            self.assertIn('ResearchFunction_'+self.target['definitions'][0]['id'], source)
            self.assertEqual(result['analysis']['expanded_target'], functions.expand_target(self.target))
            self.assertTrue(replay(output)['replayed'])

    def test_new_target_uses_the_verified_defined_function_lemma_both_routes(self):
        snapshot = self.target['definitions'][0]
        target = parse_identity('Gamma(x+2)=(x+1)*x*Gamma(x);x>0')
        target.update(lhs=call(snapshot, binary('add', variable('x'), integer(1))), definitions=[snapshot])
        uses = [{'lemma': self.package['id'], 'arguments': {'x': arg}, 'reverse': False}
                for arg in [binary('add', variable('x'), integer(1)), variable('x')]]
        from special_function_agent.real_bessel import labels
        for route in ['direct', 'steps']:
            proof = ({'mode': route, 'recipe': 'research', 'uses': uses} if route == 'direct' else
                     {'mode': route, 'steps': [{'before': target['lhs'], 'after': target['rhs'],
                        'recipe': 'research', 'uses': uses, 'reason': '定義を展開し、登録補題をx+1とxへ適用する。', 'conditions': labels(target)}]})
            output = self.location()
            result = verify({**target, 'proof': attach_lemmas(proof, [self.package])}, output)
            self.assertEqual(result['status'], 'proved', result)
            self.assertNotEqual(target_hash(target), target_hash(self.target))
            self.assertIn('ResearchLemma_'+self.package['id']+'.expanded_target', (output/'certificate.lean').read_text())
            self.assertEqual(result['research_dependencies'][0]['definitions'][0]['id'], snapshot['id'])
            self.assertTrue(replay(output)['replayed'])

    def test_definition_dependency_is_preserved_in_lean_and_record(self):
        first = self.target['definitions'][0]
        second = definition(call(first, variable('u')), 'RenamedGamma', [first])
        target = source_target(second)
        output = self.location()
        result = verify({**target, 'proof': defined_proof.default_proof(target)}, output)
        self.assertEqual(result['status'], 'proved', result)
        self.assertEqual([item['id'] for item in result['definition_dependencies']], [first['id'], second['id']])

    def test_gamma_domain_and_wrong_coefficient_never_become_proved(self):
        missing = deepcopy(self.target); missing['assumptions'] = []
        wrong = deepcopy(self.target); wrong['rhs'] = binary('mul', integer(2), wrong['rhs'])
        for target in [missing, wrong]:
            result = verify({**target, 'proof': defined_proof.default_proof(target)}, self.location())
            self.assertIn(result['status'], {'unresolved', 'needs_conditions'})

    def test_division_domain_and_pure_algebra_definition(self):
        snapshot = definition(binary('div', integer(1), variable('u')), 'Reciprocal')
        target = {'schema_version': 2, 'variables': {'x': 'real'}, 'assumptions': [],
                  'lhs': call(snapshot, variable('x')), 'rhs': call(snapshot, variable('x')), 'definitions': [snapshot]}
        self.assertEqual(verify({**target, 'proof': defined_proof.default_proof(target)}, self.location())['status'], 'needs_conditions')
        target['assumptions'] = parse_identity('Gamma(x+1)=x*Gamma(x);x>0')['assumptions']
        self.assertEqual(verify({**target, 'proof': defined_proof.default_proof(target)}, self.location())['status'], 'proved')

    def test_defined_assumption_label_and_original_lean_premise(self):
        snapshot = definition(variable('u'), 'IdentityValue')
        call_x = call(snapshot, variable('x'))
        target = {'schema_version': 2, 'variables': {'x': 'real'}, 'definitions': [snapshot],
                  'lhs': binary('mul', call_x, integer(0)), 'rhs': integer(0),
                  'assumptions': [{'op': 'expr_compare', 'lhs': call_x, 'relation': 'ne', 'rhs': integer(0)}]}
        output = self.location()
        result = verify({**target, 'proof': defined_proof.default_proof(target, 'steps')}, output)
        self.assertEqual(result['status'], 'proved', result)
        self.assertIn('(h0 : (ResearchFunction_', (output/'certificate.lean').read_text())

    def test_definition_record_tampering_is_rejected_before_lean(self):
        output = self.location()
        result = verify({**self.target, 'proof': defined_proof.default_proof(self.target)}, output)
        result['definition_dependencies'][0]['name'] = 'Changed'
        (output/'result.json').write_text(json.dumps(result))
        with patch('special_function_agent.real_special._run_lean') as run, self.assertRaises(InputError):
            replay(output)
        run.assert_not_called()

    def test_saved_statement_or_conditions_tampering_is_rejected_before_lean(self):
        import shutil
        for field, value in [('statement', '0 = 1'), ('conditions', [])]:
            output = self.location()
            shutil.copytree(self.source, output)
            result = json.loads((output/'result.json').read_text())
            result[field] = value
            (output/'result.json').write_text(json.dumps(result))
            with patch('special_function_agent.real_special._run_lean') as run, self.assertRaises(InputError):
                replay(output)
            run.assert_not_called()

    def test_missing_numerical_backend_preserves_complete_proof(self):
        with patch('special_function_agent.real_numeric.importlib.import_module', side_effect=ImportError):
            result = verify({**self.target, 'proof': defined_proof.default_proof(self.target)}, self.location())
        self.assertEqual(result['status'], 'proved', result)
        self.assertEqual(result['numerical']['diagnostic'], 'backend_unavailable')

    def test_outer_derivative_preserves_the_call_argument_and_chain_factor(self):
        snapshot = definition({'op': 'erf', 'arg': variable('u')}, 'ResearchErf')
        target = parse_identity('D_x(erf(x))=2*exp(-x^2)/sqrt(pi); x real')
        target['lhs']['arg'] = call(snapshot, variable('x'))
        target['definitions'] = [snapshot]
        wrong = deepcopy(target)
        wrong['lhs']['arg']['arguments']['u'] = binary('mul', integer(2), variable('x'))
        for route in ['direct', 'steps']:
            good = verify({**target, 'proof': defined_proof.default_proof(target, route)}, self.location())
            self.assertEqual(good['status'], 'proved', good)
            bad = verify({**wrong, 'proof': defined_proof.default_proof(wrong, route)}, self.location())
            self.assertNotEqual(bad['status'], 'proved', bad)
