"""Analytic contracts, original function calls, and reused source proofs stay fixed."""
from copy import deepcopy
import json
import os
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch

from special_function_agent import core, defined_proof, research_functions as functions
from special_function_agent import research_function_library, research_library
from special_function_agent.archive import target_hash
from special_function_agent.real_bessel import labels
from special_function_agent.research_generation import attach_lemmas

EXAMPLES = core.ROOT/'examples'
SLUGS = ('exp-series', 'gaussian-primitive', 'linear-ivp')
MODULE = 'SpecialFunctionProofAgent/AnalyticDefinitions.lean'


def example(slug, kind):
    return core.load_json(EXAMPLES/f'research-analytic-{slug}.{kind}.json')


def integer(value): return {'op': 'int', 'value': value}
def variable(name): return {'op': 'var', 'name': name}
def binary(op, left, right): return {'op': op, 'args': [left, right]}


def source_request(slug, route='direct'):
    target = example(slug, 'source.target')
    return {**target, 'proof': defined_proof.default_proof(target, route)}


def derived_request(slug, package, route):
    target = example(slug, 'derived.target')
    uses = [{'lemma': package['id'], 'arguments': {name: variable(name) for name in target['variables']},
             'reverse': False}]
    proof = ({'mode': 'direct', 'recipe': 'research', 'uses': uses} if route == 'direct' else
             {'mode': 'steps', 'steps': [{'before': target['lhs'], 'after': target['rhs'],
               'recipe': 'research', 'uses': uses, 'reason': '元の解析定義の等式を適用し、両辺を2倍する。',
               'conditions': labels(target)}]})
    return {**target, 'proof': attach_lemmas(proof, [package])}


class ResearchAnalyticBoundaryTests(unittest.TestCase):
    def test_examples_preserve_semantic_ids_original_calls_and_all_real_parameters(self):
        for slug in SLUGS:
            with self.subTest(slug=slug):
                raw = example(slug, 'definition')
                snapshot = functions.make_definition(raw)
                source = example(slug, 'source.target')
                self.assertEqual(source['definitions'], [snapshot])
                self.assertEqual(source['lhs']['function'], snapshot['id'])
                self.assertEqual(example(slug, 'source.input'), {k: v for k, v in source.items() if k != 'definitions'})
                self.assertTrue(all(kind == 'real' for kind in source['variables'].values()))
                self.assertEqual(source['assumptions'], [])
                self.assertEqual(functions.expand_target(source)['lhs'], source['rhs'])
                self.assertNotEqual(target_hash(source), target_hash(example(slug, 'derived.target')))
                for route in ('direct', 'steps'):
                    core.validate_request(source_request(slug, route))

    def test_definition_certificate_contains_the_actual_analytic_contract(self):
        for slug, proposition, theorem in (
                ('exp-series', 'HasSum', 'hasSum_exponentialSeries'),
                ('gaussian-primitive', 'IntervalIntegrable', 'intervalIntegrable_gaussian'),
                ('linear-ivp', '∃! y : ℝ → ℝ', 'existsUnique_homogeneousIVPSolution')):
            with self.subTest(slug=slug):
                snapshot = functions.make_definition(example(slug, 'definition'))
                certificate = functions.render_definition(snapshot)
                target = certificate.split('theorem target', 1)[1]
                self.assertIn(proposition, target)
                self.assertIn('SpecialFunctionProofAgent.'+theorem, target)
                self.assertIn('SpecialFunctionProofAgent.AnalyticDefinitions', certificate)
                self.assertIn('BESSEL_AUDIT_BEGIN', certificate)
                self.assertNotIn('sorry', certificate)

    def test_general_term_integrand_initial_time_and_nested_primitives_are_rejected(self):
        for operation in ([], {}, None):
            raw = example('exp-series', 'definition'); raw['body']['op'] = operation
            with self.subTest(operation=operation), self.assertRaises(core.InputError):
                functions.make_definition(raw)
        mutations = [('exp-series', 'term', variable('u')),
                     ('gaussian-primitive', 'integrand', variable('u')),
                     ('linear-ivp', 'initial_time', integer(1)),
                     ('linear-ivp', 'equation', "y'=rate*y+1")]
        for slug, field, value in mutations:
            raw = example(slug, 'definition'); raw['body'][field] = value
            with self.subTest(slug=slug, field=field), self.assertRaises(core.InputError):
                functions.make_definition(raw)
        for op in ('exp_series', 'gaussian_primitive'):
            raw = example('exp-series', 'definition')
            raw['body']['arg'] = {'op': op, 'arg': variable('u')}
            with self.subTest(op=op), self.assertRaises(core.InputError):
                functions.make_definition(raw)
        raw = example('linear-ivp', 'definition')
        raw['body']['rate'] = variable('missing')
        with self.assertRaises(core.InputError): functions.make_definition(raw)
        raw = example('linear-ivp', 'definition'); raw['parameters']['a'] = 'nat'
        with self.assertRaises(core.InputError): functions.make_definition(raw)

    def test_finite_dependency_composition_retains_the_analytic_definition_and_contract(self):
        base = functions.make_definition(example('exp-series', 'definition'))
        outer = functions.make_definition({'schema_version': 1, 'name': 'DoubleSeries',
            'parameters': {'v': 'real'}, 'body': binary('mul', integer(2),
                {'op': 'defined', 'function': base['id'], 'arguments': {'u': variable('v')}}),
            'definitions': [base]})
        self.assertEqual([item['id'] for item in functions.metadata([outer])], [base['id'], outer['id']])
        self.assertIn('hasSum_exponentialSeries', functions.render_definition(outer))
        self.assertIn(MODULE, functions.environment(outer))
        forbidden = example('exp-series', 'definition')
        forbidden['definitions'] = [base]
        forbidden['name'] = 'NestedSeries'
        forbidden['body']['arg'] = {'op': 'defined', 'function': base['id'], 'arguments': {'u': variable('u')}}
        with self.assertRaises(core.InputError): functions.make_definition(forbidden)

    def test_optional_environment_hash_preserves_semantic_target_identity(self):
        target = example('linear-ivp', 'source.target')
        baseline = core.environment()
        self.assertNotIn(MODULE, baseline)
        scoped = functions.environment(target)
        self.assertEqual({k: v for k, v in scoped.items() if k != MODULE}, baseline)
        self.assertIn(MODULE, scoped)
        original_id = target_hash(target)
        changed = {**baseline, 'environment-test': 'changed'}
        with patch.object(core, 'environment', return_value=changed):
            self.assertEqual(target_hash(target), original_id)
            self.assertNotEqual(functions.environment(target), scoped)

    def test_gamma_and_denominator_conditions_are_checked_after_expansion(self):
        for child in ({'op': 'gamma', 'arg': variable('u')}, binary('div', integer(1), variable('u'))):
            raw = example('exp-series', 'definition'); raw['body']['arg'] = child
            snapshot = functions.make_definition(raw)
            target = example('exp-series', 'source.target')
            target['definitions'] = [snapshot]
            target['lhs']['function'] = snapshot['id']
            target['rhs'] = functions.expand_expr(target['lhs'], [snapshot])
            request = {**target, 'proof': defined_proof.default_proof(target)}
            with tempfile.TemporaryDirectory(prefix='sf-analytic-domain-') as temporary, \
                 patch('special_function_agent.real_special._run_lean') as run:
                result = core.verify(request, Path(temporary)/'missing')
                self.assertEqual(result['status'], 'needs_conditions', result)
                run.assert_not_called()


@unittest.skipUnless(os.environ.get('SF_RUN_LEAN_TESTS') == '1', 'Set SF_RUN_LEAN_TESTS=1 for analytic definition Lean acceptance.')
class ResearchAnalyticLeanTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temporary = tempfile.TemporaryDirectory(prefix='sf-analytic-integration-')
        cls.root = Path(cls.temporary.name)
        cls.packages, cls.source_results = {}, {}
        for slug in SLUGS:
            package = research_function_library.register(example(slug, 'definition'), cls.root/'research', timeout=120)
            if package['verification']['status'] != 'defined': raise AssertionError(package)
            source = cls.root/slug
            result = core.verify(source_request(slug), source, timeout=120)
            if result.get('status') != 'proved': raise AssertionError(result)
            cls.source_results[slug] = result
            cls.packages[slug] = research_library.register(source, cls.root/'research', name=slug, timeout=120)

    @classmethod
    def tearDownClass(cls): cls.temporary.cleanup()

    def location(self): return Path(tempfile.mkdtemp(dir=self.root))/'run'

    def test_all_three_source_identities_direct_steps_and_replay(self):
        for slug in SLUGS:
            with self.subTest(slug=slug):
                direct = self.source_results[slug]
                self.assertTrue(direct['full_function_proof'])
                self.assertIn(MODULE, direct['environment'])
                output = self.location()
                result = core.verify(source_request(slug, 'steps'), output, timeout=120)
                self.assertEqual(result['status'], 'proved', result)
                self.assertTrue(core.replay(output, timeout=120)['replayed'])
                source = (output/'certificate.lean').read_text()
                self.assertIn('theorem target', source)
                self.assertIn('theorem expanded_target', source)
                self.assertIn('ResearchFunction_', source)

    def test_all_three_source_lemmas_prove_distinct_targets_in_both_routes(self):
        for slug in SLUGS:
            for route in ('direct', 'steps'):
                with self.subTest(slug=slug, route=route):
                    output = self.location()
                    result = core.verify(derived_request(slug, self.packages[slug], route), output, timeout=120)
                    self.assertEqual(result['status'], 'proved', result)
                    self.assertEqual(result['research_dependencies'][0]['id'], self.packages[slug]['id'])
                    self.assertIn('ResearchLemma_'+self.packages[slug]['id']+'.expanded_target',
                                  (output/'certificate.lean').read_text())
                    if route == 'steps': self.assertTrue(core.replay(output, timeout=120)['replayed'])

    def test_negative_gaussian_orientation_and_zero_ivp_parameters(self):
        gaussian = example('gaussian-primitive', 'source.target')
        gaussian['lhs']['arguments']['u'] = integer(-2)
        gaussian['rhs'] = functions.expand_expr(gaussian['lhs'], gaussian['definitions'])
        cases = [gaussian]
        for rate, initial in ((0, 3), (-2, 0)):
            ivp = example('linear-ivp', 'source.target')
            ivp['lhs']['arguments'].update(a=integer(rate), c=integer(initial))
            ivp['rhs'] = functions.expand_expr(ivp['lhs'], ivp['definitions'])
            cases.append(ivp)
        for target in cases:
            with self.subTest(lhs=target['lhs']):
                result = core.verify({**target, 'proof': defined_proof.default_proof(target)}, self.location(), timeout=120)
                self.assertEqual(result['status'], 'proved', result)

    def test_wrong_coefficient_and_swapped_ivp_parameters_remain_unresolved(self):
        target = example('exp-series', 'source.target')
        target['rhs'] = binary('mul', integer(2), target['rhs'])
        swapped = example('linear-ivp', 'source.target')
        swapped['lhs']['arguments'].update(a=variable('c'), c=variable('a'))
        for invalid in (target, swapped):
            with self.subTest(lhs=invalid['lhs']):
                output = self.location()
                result = core.verify({**invalid, 'proof': defined_proof.default_proof(invalid)}, output, timeout=120)
                self.assertNotEqual(result['status'], 'proved', result)
                self.assertFalse((output/'certificate.lean').exists())

    def test_saved_contracts_source_and_statement_tampering_are_rejected(self):
        for kind in ('source', 'metadata', 'statement'):
            output = self.location()
            shutil.copytree(self.root/'linear-ivp', output)
            if kind == 'source':
                with (output/'certificate.lean').open('a') as stream: stream.write('\n-- changed certificate\n')
            else:
                result = core.load_json(output/'result.json')
                if kind == 'metadata': result['definition_dependencies'][0]['analytic_contracts'][0]['semantics']['initial_condition']['time'] = 1
                else: result['statement'] = '0 = 1'
                (output/'result.json').write_text(json.dumps(result))
            with self.subTest(kind=kind), patch('special_function_agent.real_special._run_lean') as run:
                with self.assertRaises(core.InputError): core.replay(output, timeout=120)
                run.assert_not_called()

    def test_finite_definition_dependency_and_missing_numeric_backend(self):
        base = example('exp-series', 'source.target')['definitions'][0]
        outer = functions.make_definition({'schema_version': 1, 'name': 'DoubleSeries', 'parameters': {'v': 'real'},
            'body': binary('mul', integer(2), {'op': 'defined', 'function': base['id'], 'arguments': {'u': variable('v')}}),
            'definitions': [base]})
        target = example('exp-series', 'derived.target')
        target['definitions'] = [outer]
        target['lhs'] = {'op': 'defined', 'function': outer['id'], 'arguments': {'v': variable('x')}}
        with patch('special_function_agent.real_numeric.importlib.import_module', side_effect=ImportError):
            result = core.verify({**target, 'proof': defined_proof.default_proof(target)}, self.location(), timeout=120)
        self.assertEqual(result['status'], 'proved', result)
        self.assertEqual(result['numerical']['diagnostic'], 'backend_unavailable')
        self.assertEqual([item['id'] for item in result['definition_dependencies']], [base['id'], outer['id']])


if __name__ == '__main__':
    unittest.main()
