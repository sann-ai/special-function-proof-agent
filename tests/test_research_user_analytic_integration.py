"""User-selected analytic formulas retain their bindings, domains, and evidence."""
from copy import deepcopy
import hashlib
import json
import os
from pathlib import Path
import shutil
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from special_function_agent import core, defined_proof, research_functions as functions
from special_function_agent import research_function_library, research_library
from special_function_agent.archive import target_hash
from special_function_agent.generate import generate
from special_function_agent.real_bessel import labels, _walk
from special_function_agent.research_generation import attach_lemmas

SLUGS = ('series', 'integral', 'ode')
MODULE = 'SpecialFunctionProofAgent/UserAnalyticDefinitions.lean'


def example(slug, kind):
    return core.load_json(core.ROOT/'examples'/f'research-user-{slug}.{kind}.json')


def integer(value): return {'op': 'int', 'value': value}
def variable(name): return {'op': 'var', 'name': name}
def binary(op, left, right): return {'op': op, 'args': [left, right]}
def power(base, exponent): return {'op': 'pow', 'base': base, 'exponent': exponent}
def add(left, right): return binary('add', left, right)
def sub(left, right): return binary('sub', left, right)
def mul(left, right): return binary('mul', left, right)
def div(left, right): return binary('div', left, right)
def exp(arg): return {'op': 'exp', 'arg': arg}
def kernel(arg): return div(power(arg, variable('k')), {'op': 'factorial', 'arg': variable('k')})


def request(target, route='direct'):
    return {**deepcopy(target), 'proof': defined_proof.default_proof(target, route)}


def replace_definition(target, raw):
    target = deepcopy(target)
    snapshot = functions.make_definition(raw)
    target['definitions'] = [snapshot]
    target['lhs']['function'] = snapshot['id']
    return target


def derived_request(slug, package, route):
    target = example(slug, 'derived.target')
    uses = [{'lemma': package['id'], 'arguments': {name: variable(name) for name in target['variables']}, 'reverse': False}]
    proof = ({'mode': 'direct', 'recipe': 'research', 'uses': uses} if route == 'direct' else
             {'mode': 'steps', 'steps': [{'before': target['lhs'], 'after': target['rhs'],
                 'recipe': 'research', 'uses': uses, 'reason': '元のユーザー式の補題を適用し、両辺を2倍する。',
                 'conditions': labels(target)}]})
    return {**target, 'proof': attach_lemmas(proof, [package])}


def outer_binding_target(kind):
    snapshot = functions.make_definition(example('integral', 'definition'))
    call = {'op': 'defined', 'function': snapshot['id'],
            'arguments': {'a': integer(0), 'b': integer(1), 'x': variable('t')}}
    if kind == 'deriv':
        lhs = {'op': 'deriv', 'var': 't', 'arg': call}
        variables = {'t': 'real'}
    else:
        lhs = {'op': 'integral', 'var': 't', 'lower': integer(-1), 'upper': integer(2), 'body': call}
        variables = {'u': 'real'}
    return {'schema_version': 2, 'variables': variables, 'assumptions': [], 'definitions': [snapshot],
            'lhs': lhs, 'rhs': functions.expand_expr(lhs, [snapshot])}


def zero_target(body):
    raw = {'schema_version': 1, 'name': 'CancelledScalar', 'parameters': {'a': 'real'},
           'body': body, 'definitions': []}
    snapshot = functions.make_definition(raw)
    return {'schema_version': 2, 'variables': {'a': 'real'}, 'assumptions': [], 'definitions': [snapshot],
            'lhs': {'op': 'defined', 'function': snapshot['id'], 'arguments': {'a': variable('a')}}, 'rhs': integer(0)}


def rehash(package):
    package['manifest'] = {name: hashlib.sha256(text.encode()).hexdigest() for name, text in package['evidence'].items()}
    package['id'] = hashlib.sha256(json.dumps({key: value for key, value in package.items() if key != 'id'},
        ensure_ascii=False, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
    return package


class UserAnalyticIntegrationBoundaryTests(unittest.TestCase):
    def test_examples_keep_original_formulas_parameters_and_semantic_definition_ids(self):
        for slug in SLUGS:
            with self.subTest(slug=slug):
                raw = example(slug, 'definition')
                target = example(slug, 'source.target')
                snapshot = functions.make_definition(raw)
                self.assertEqual(target['definitions'], [snapshot])
                self.assertEqual(target['lhs']['function'], snapshot['id'])
                self.assertEqual(example(slug, 'source.input'), {k: v for k, v in target.items() if k != 'definitions'})
                self.assertEqual(target['assumptions'], [])
                self.assertEqual(target['variables'], raw['parameters'])
                contract = functions.metadata([snapshot])[0]['analytic_contracts'][0]
                self.assertEqual(contract['semantics']['original'], raw['body'])
                self.assertEqual(contract['semantics']['normalized']['original'], raw['body'])
                self.assertNotEqual(target_hash(target), target_hash(example(slug, 'derived.target')))
                for route in ('direct', 'steps'):
                    data = request(target, route)
                    core.validate_request(data)
                    self.assertEqual(target_hash(data), target_hash(target))
                    self.assertEqual({k: v for k, v in data.items() if k != 'proof'}, target)

    def test_registration_certificate_includes_the_original_analytic_contract(self):
        for slug, proposition, theorem in (
                ('series', 'HasSum', 'hasSum_factorialCombination'),
                ('integral', 'IntervalIntegrable', 'intervalIntegrable_evalPolynomial'),
                ('ode', '∃! y : ℝ → ℝ', 'existsUnique_polynomialIVPSolution')):
            with self.subTest(slug=slug):
                snapshot = functions.make_definition(example(slug, 'definition'))
                source = functions.render_definition(snapshot)
                self.assertIn(proposition, source.split('theorem target', 1)[1])
                self.assertIn(theorem, source)
                self.assertIn('import SpecialFunctionProofAgent.UserAnalyticDefinitions', source)
                self.assertIn('BESSEL_AUDIT_BEGIN', source)
                self.assertNotIn('sorry', source)
                self.assertIn(MODULE, functions.environment(snapshot))
                self.assertNotIn(MODULE, core.environment())

    def test_same_named_external_binding_is_scoped_and_parameter_capture_is_rejected(self):
        for kind in ('deriv', 'integral'):
            with self.subTest(kind=kind):
                target = outer_binding_target(kind)
                core.validate_request(request(target))
                expanded = functions.expand_target(target)
                self.assertEqual(expanded['lhs'], target['rhs'])
                self.assertEqual(expanded['lhs']['var'], 't')
                child = expanded['lhs']['arg'] if kind == 'deriv' else expanded['lhs']['body']
                self.assertIn(variable('t'), list(_walk(child)))
                source = defined_proof.render(request(target))
                self.assertIn('∫ ut0', source)
                self.assertIn('fun (d1 : ℝ)' if kind == 'deriv' else '∫ b1', source)
        raw = example('integral', 'definition')
        raw['body']['var'] = 'x'
        with self.assertRaises(core.InputError): functions.make_definition(raw)

    def test_cancelled_scalar_domains_and_bound_divisors_still_require_conditions(self):
        a, t, y = variable('a'), variable('t'), variable('y')
        quotient = div(t, a)
        bodies = [
            {'op': 'integral_definition', 'var': 't', 'integrand': sub(quotient, quotient), 'lower': integer(0), 'upper': integer(1)},
            {'op': 'ode_definition', 'var': 't', 'state': 'y', 'rhs': sub(mul(quotient, y), mul(quotient, y)),
             'initial_time': integer(0), 'initial_value': integer(0), 'arg': integer(1)},
            {'op': 'series_definition', 'index': 'k', 'term': mul(integer(0), div(kernel(integer(2)), a))}]
        for scalar in ({'op': 'gamma', 'arg': a}, {'op': 'bessel_j', 'order': integer(0), 'arg': a}, div(integer(1), integer(0))):
            term = mul(scalar, t)
            bodies.append({'op': 'integral_definition', 'var': 't', 'integrand': sub(term, term),
                           'lower': integer(0), 'upper': integer(1)})
        for body in bodies[:-1]:
            with self.subTest(body=body), tempfile.TemporaryDirectory(prefix='sf-user-domain-') as temporary, \
                 patch('special_function_agent.real_special._run_lean') as lean:
                data = request(zero_target(body))
                result = core.verify(data, Path(temporary)/'run', timeout=120)
                self.assertEqual(result['status'], 'needs_conditions', result)
                self.assertEqual(core.load_json(Path(temporary)/'run/request.json')['assumptions'], [])
                lean.assert_not_called()
        with patch('special_function_agent.real_special._run_lean') as lean:
            with self.assertRaisesRegex(core.NeedsConditions, 'identically zero'):
                request(zero_target(bodies[-1]))
            lean.assert_not_called()

    def test_candidate_authority_and_original_assumptions_are_fixed_before_verification(self):
        target = example('ode', 'source.target')
        target['assumptions'] = [{'op': 'compare', 'variable': 'c', 'relation': 'ge',
                                  'value': {'numerator': 0, 'denominator': 1}}]
        original = deepcopy(target)
        proof = defined_proof.default_proof(target, 'steps')
        self.assertEqual(functions.expand_target(request(target, 'steps'))['assumptions'], original['assumptions'])
        self.assertEqual(proof['steps'][0]['conditions'], labels(original))
        for extra, value in [('target', {**target, 'rhs': integer(0)}), ('assumptions', []),
                             ('definitions', []), ('lean', 'axiom injected : False')]:
            with self.subTest(extra=extra), self.assertRaises(core.InputError):
                core.validate_request({**target, 'proof': {**proof, extra: value}})
        altered = deepcopy(proof)
        altered['steps'][0]['before'] = functions.expand_target(target)['lhs']
        with self.assertRaises(core.InputError): core.validate_request({**target, 'proof': altered})
        self.assertEqual(target, original)

    def test_mocked_ai_plan_preserves_the_exact_user_target(self):
        target = example('series', 'source.target')
        proof = defined_proof.default_proof(target)
        def process(command, **kwargs):
            Path(command[command.index('--output-last-message')+1]).write_text(json.dumps(proof))
            return SimpleNamespace(returncode=0, communicate=lambda **kwargs: ('', ''))
        with tempfile.TemporaryDirectory(prefix='sf-user-ai-') as temporary, \
             patch('special_function_agent.generate.shutil.which', return_value='/bin/codex'), \
             patch('special_function_agent.generate.subprocess.Popen', side_effect=process), \
             patch('special_function_agent.generate.verify', return_value={'status': 'proved'}) as verify:
            generate(target, 'direct', Path(temporary)/'run')
            received = verify.call_args.args[0]
        self.assertEqual({key: value for key, value in received.items() if key != 'proof'}, target)
        self.assertEqual(received['proof'], proof)


@unittest.skipUnless(os.environ.get('SF_RUN_LEAN_TESTS') == '1', 'Set SF_RUN_LEAN_TESTS=1 for user analytic Lean integration.')
class UserAnalyticIntegrationLeanTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temporary = tempfile.TemporaryDirectory(prefix='sf-user-analytic-integration-')
        cls.root = Path(cls.temporary.name)
        cls.packages, cls.results, cls.function_packages = {}, {}, {}
        for slug in SLUGS:
            package = research_function_library.register(example(slug, 'definition'), cls.root/'research', timeout=120)
            if package['verification']['status'] != 'defined': raise AssertionError(package)
            cls.function_packages[slug] = package
            output = cls.root/slug
            result = core.verify(request(example(slug, 'source.target')), output, timeout=120)
            if result['status'] != 'proved': raise AssertionError({'slug': slug, 'output': str(output), 'result': result})
            cls.results[slug] = result
            cls.packages[slug] = research_library.register(output, cls.root/'research', name='user-'+slug, timeout=120)

    @classmethod
    def tearDownClass(cls): cls.temporary.cleanup()

    def location(self): return Path(tempfile.mkdtemp(dir=self.root))/'run'

    def test_source_registration_direct_steps_and_replay(self):
        for slug in SLUGS:
            with self.subTest(slug=slug):
                self.assertTrue(self.function_packages[slug]['verification']['accepted'])
                self.assertTrue(self.results[slug]['full_function_proof'])
                self.assertEqual(set(self.function_packages[slug]['verification']['axioms']), {'propext', 'Quot.sound', 'Classical.choice'})
                output = self.location()
                result = core.verify(request(example(slug, 'source.target'), 'steps'), output, timeout=120)
                self.assertEqual(result['status'], 'proved', result)
                self.assertTrue(core.replay(output, timeout=120)['replayed'])
                certificate = (output/'certificate.lean').read_text()
                self.assertIn('theorem expanded_target', certificate)
                self.assertIn('theorem target', certificate)
                self.assertIn('ResearchAnalytic_', certificate)

    def test_explicit_nonzero_premise_proves_the_cancelled_integral_and_replays(self):
        quotient = div(variable('t'), variable('a'))
        body = {'op': 'integral_definition', 'var': 't', 'integrand': sub(quotient, quotient),
                'lower': integer(0), 'upper': integer(1)}
        target = zero_target(body)
        target['assumptions'] = [{'op': 'compare', 'variable': 'a', 'relation': 'ne',
                                  'value': {'numerator': 0, 'denominator': 1}}]
        output = self.location()
        result = core.verify(request(target), output, timeout=120)
        self.assertEqual(result['status'], 'proved', result)
        self.assertTrue(core.replay(output, timeout=120)['replayed'])
        saved = core.load_json(output/'request.json')
        self.assertEqual({key: value for key, value in saved.items() if key != 'proof'}, target)
        declaration = (output/'certificate.lean').read_text().split('theorem target', 1)[1].split(':= by', 1)[0]
        self.assertIn('h0 :', declaration)
        self.assertIn('≠', declaration)
        self.assertNotIn('h1 :', declaration)
        contract = result['definition_dependencies'][0]['analytic_contracts'][0]
        self.assertEqual(contract['semantics']['original'], body)
        self.assertEqual(contract['semantics']['normalized']['nonzero_denominators'], [variable('a')])
        self.assertEqual(core.load_json(output/'analysis.json')['definitions'][0]['analytic_contracts'][0], contract)

    def test_source_lemmas_prove_distinct_doubled_targets_in_both_routes(self):
        for slug in SLUGS:
            for route in ('direct', 'steps'):
                with self.subTest(slug=slug, route=route):
                    output = self.location()
                    result = core.verify(derived_request(slug, self.packages[slug], route), output, timeout=120)
                    self.assertEqual(result['status'], 'proved', result)
                    self.assertEqual(result['research_dependencies'][0]['id'], self.packages[slug]['id'])
                    self.assertIn('ResearchLemma_'+self.packages[slug]['id']+'.expanded_target', (output/'certificate.lean').read_text())
                    if route == 'steps': self.assertTrue(core.replay(output, timeout=120)['replayed'])

    def test_different_series_reversed_interval_and_arbitrary_initial_time(self):
        series_raw = example('series', 'definition')
        series_raw['body']['term'] = sub(mul(integer(3), kernel(mul(integer(2), variable('x')))), kernel(variable('x')))
        series_target = replace_definition(example('series', 'source.target'), series_raw)
        series_target['rhs'] = sub(mul(integer(3), exp(mul(integer(2), variable('x')))), exp(variable('x')))
        integral_raw = example('integral', 'definition')
        integral_raw['body'].update(lower=integer(2), upper=integer(-3))
        integral_target = replace_definition(example('integral', 'source.target'), integral_raw)
        integral_target['rhs'] = div(sub(power(add(integer(-3), variable('x')), 3), power(add(integer(2), variable('x')), 3)), integer(3))
        ode_raw = example('ode', 'definition')
        ode_raw['body'].update(initial_time=variable('a'), initial_value=integer(0))
        ode_target = replace_definition(example('ode', 'source.target'), ode_raw)
        ode_target['rhs'] = integer(0)
        for slug, target in zip(SLUGS, (series_target, integral_target, ode_target)):
            with self.subTest(slug=slug):
                result = core.verify(request(target), self.location(), timeout=120)
                self.assertEqual(result['status'], 'proved', result)

    def test_wrong_coefficient_endpoints_initial_value_and_rhs_cannot_prove_false_equations(self):
        wrong_series = example('series', 'source.target')
        wrong_series['rhs'] = add(wrong_series['rhs'], integer(1))
        wrong_interval = example('integral', 'source.target')
        wrong_interval['lhs']['arguments'].update(a=variable('b'), b=variable('a'))
        raw = example('ode', 'definition')
        raw['body']['initial_value'] = add(variable('c'), integer(1))
        wrong_initial = replace_definition(example('ode', 'source.target'), raw)
        raw = example('ode', 'definition')
        raw['body']['rhs']['args'][0]['args'][1] = integer(3)
        wrong_rhs = replace_definition(example('ode', 'source.target'), raw)
        for kind, target in zip(('coefficient', 'endpoints', 'initial_value', 'rhs'), (wrong_series, wrong_interval, wrong_initial, wrong_rhs)):
            with self.subTest(kind=kind):
                output = self.location()
                result = core.verify(request(target), output, timeout=120)
                self.assertNotEqual(result['status'], 'proved', result)
                self.assertFalse((output/'certificate.lean').exists())

    def test_internal_time_and_outer_calculus_binders_keep_distinct_meanings(self):
        for kind in ('deriv', 'integral'):
            with self.subTest(kind=kind):
                result = core.verify(request(outer_binding_target(kind)), self.location(), timeout=120)
                self.assertEqual(result['status'], 'proved', result)

    def test_rehashed_snapshot_and_saved_evidence_tampering_are_rejected(self):
        for kind in ('certificate', 'contract'):
            package = deepcopy(self.packages['ode'])
            if kind == 'certificate': package['evidence']['certificate.lean'] += '\naxiom injected : False\n'
            else:
                result = json.loads(package['evidence']['result.json'])
                result['definition_dependencies'][0]['analytic_contracts'][0]['semantics']['original']['initial_time'] = integer(0)
                package['evidence']['result.json'] = json.dumps(result)
            rehash(package)
            with self.subTest(kind=kind), patch('special_function_agent.real_special._run_lean') as lean:
                with self.assertRaises(core.InputError): core.validate_request(derived_request('ode', package, 'direct'))
                lean.assert_not_called()
        for kind in ('source', 'analysis'):
            output = self.location()
            shutil.copytree(self.root/'series', output)
            if kind == 'source':
                with (output/'certificate.lean').open('a') as stream: stream.write('\n-- changed\n')
            else:
                data = core.load_json(output/'analysis.json')
                data['definitions'][0]['analytic_contracts'][0]['semantics']['original']['index'] = 'j'
                (output/'analysis.json').write_text(json.dumps(data))
            with self.subTest(kind=kind), patch('special_function_agent.real_special._run_lean') as lean:
                with self.assertRaises(core.InputError): core.replay(output, timeout=120)
                lean.assert_not_called()


if __name__ == '__main__':
    unittest.main()
