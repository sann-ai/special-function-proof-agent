"""Full real Gamma/Beta certificates and their fixed-target trust boundary."""
import copy
import importlib.util
import json
import os
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from special_function_agent import archive
from special_function_agent.core import (
    ALLOWED_AXIOMS, InputError, NeedsConditions, render_lean, replay,
    validate_request, verify,
)
from special_function_agent.generate import generate
from special_function_agent.parser import parse_identity
from special_function_agent.real_numeric import diagnose
from special_function_agent.real_special import default_proof, has_special, match_identity


RECURRENCE = 'Gamma(x+1)=x*Gamma(x);x>0'
BETA = ('int(0,1,t^(a-1)*(1-t)^(b-1),t)='
        'Gamma(a)*Gamma(b)/Gamma(a+b);a>0,b>0')
SCALED = ('int(0,infinity,t^(a-1)*exp(-r*t),t)='
          'r^(-a)*Gamma(a);a>0,r>0')
FORMULAS = {'gamma_recurrence': RECURRENCE, 'beta_integral': BETA,
            'gamma_scaled_integral': SCALED}
RUN_LEAN = any(os.environ.get(name) == '1'
               for name in ('SF_RUN_LEAN_TESTS', 'BESSEL_RUN_LEAN_TESTS'))


def request(text=RECURRENCE, route='direct'):
    target = parse_identity(text)
    return {**target, 'proof': default_proof(target, route)}


class SpecialFunctionBoundaryTests(unittest.TestCase):
    def test_three_formulas_keep_real_integrals_and_free_variables(self):
        for recipe, text in FORMULAS.items():
            with self.subTest(recipe=recipe):
                data = request(text)
                validate_request(data)
                self.assertTrue(has_special(data))
                self.assertEqual(match_identity(data['lhs'], data['rhs'])['recipe'], recipe)
                self.assertEqual(data['proof'], {'mode': 'direct', 'recipe': recipe})
                source = render_lean(data)
                self.assertIn('SpecialFunctionProofAgent.' + recipe, source)
                self.assertIn('Real.Gamma', source)
                self.assertNotIn('axiom ', source)
                self.assertNotIn('sorry', source)
                if recipe != 'gamma_recurrence':
                    self.assertNotIn('t', data['variables'])
                    self.assertEqual(data['lhs']['op'], 'integral')
                    self.assertIn('Real.rpow', source)
                if recipe == 'gamma_scaled_integral':
                    self.assertEqual(data['lhs']['upper'], {'op': 'infinity'})
                    self.assertIn('Set.Ioi', source)
                    self.assertIn('Real.exp', source)

    def test_renamed_parameters_bound_variable_and_reverse_formula(self):
        text = ('int(0,1,u^(shape-1)*(1-u)^(width-1),u)='
                'Gamma(shape)*Gamma(width)/Gamma(shape+width);shape>0,width>0')
        data = request(text, 'steps')
        self.assertEqual(data['variables'], {'shape': 'real', 'width': 'real'})
        self.assertEqual(data['lhs']['var'], 'u')
        matched = match_identity(data['rhs'], data['lhs'])
        self.assertEqual(matched['recipe'], 'beta_integral')
        self.assertTrue(matched['reverse'])
        data['lhs'], data['rhs'] = data['rhs'], data['lhs']
        data['proof'] = default_proof(data, 'direct')
        self.assertIn('.symm', render_lean(data))
        grouped = request(SCALED.replace('exp(-r*t)', 'exp(-(r*t))'))
        self.assertEqual(grouped['proof']['recipe'], 'gamma_scaled_integral')

    def test_three_variables_and_every_unused_condition_remain_in_target(self):
        data = request('Gamma(shape+1)=shape*Gamma(shape);shape>0,aux>2,other<4')
        self.assertEqual(data['variables'], {'aux': 'real', 'other': 'real', 'shape': 'real'})
        source = render_lean(data)
        self.assertIn('(v0 : ℝ) (v1 : ℝ) (v2 : ℝ)', source)
        self.assertIn('(h0 : v2 > (0 / 1 : ℝ))', source)
        self.assertIn('(h1 : v0 > (2 / 1 : ℝ))', source)
        self.assertIn('(h2 : v1 < (4 / 1 : ℝ))', source)
        changed = copy.deepcopy(data)
        changed['assumptions'].pop()
        self.assertNotEqual(archive.target_hash(data), archive.target_hash(changed))

    def test_special_recipe_cannot_accept_wrong_coefficient(self):
        for recipe, text in FORMULAS.items():
            data = request(text)
            data['rhs'] = {'op': 'mul', 'args': [{'op': 'int', 'value': 2}, data['rhs']]}
            self.assertIsNone(match_identity(data['lhs'], data['rhs']))
            with self.subTest(recipe=recipe), self.assertRaises(InputError):
                render_lean(data)

    def test_structured_steps_preserve_endpoints_conditions_and_lean_source(self):
        data = request(BETA, 'steps')
        source = render_lean(data)
        altered = copy.deepcopy(data)
        altered['proof']['steps'][0]['reason'] = '\nend BesselAgentCandidate\naxiom forged : False'
        self.assertEqual(render_lean(altered), source)
        for mutation in ('before', 'after', 'conditions', 'assumptions', 'recipe'):
            altered = copy.deepcopy(data)
            step = altered['proof']['steps'][0]
            if mutation in {'before', 'after'}:
                step[mutation] = {'op': 'int', 'value': 0}
            elif mutation == 'conditions':
                step['conditions'].append('False')
            elif mutation == 'assumptions':
                altered['proof']['assumptions'] = ['False']
            else:
                step['recipe'] = 'exact h0\naxiom forged : False'
            with self.subTest(mutation=mutation), self.assertRaises(InputError):
                validate_request(altered)
        altered = request()
        altered['proof']['assumptions'] = ['lhs = rhs']
        with self.assertRaises(InputError):
            validate_request(altered)

    def test_target_assumption_and_bound_variable_capture_are_rejected(self):
        with self.assertRaises(NeedsConditions):
            parse_identity('Gamma(x)=0;x>0,Gamma(x)=0')
        for mutation in ('capture', 'undeclared', 'infinity', 'source'):
            data = request(BETA)
            if mutation == 'capture':
                data['lhs']['var'] = 'a'
            elif mutation == 'undeclared':
                data['lhs']['body']['args'][0]['base']['name'] = 'hidden'
            elif mutation == 'infinity':
                data['lhs']['upper']['op'] = 'infinity'
            else:
                data['variables'] = {'a) : False := by sorry --': 'real', 'b': 'real'}
            with self.subTest(mutation=mutation), self.assertRaises(InputError):
                validate_request(data)

    def test_missing_positive_or_singular_parameters_never_invoke_lean(self):
        cases = [RECURRENCE.replace('x>0', 'x>=0'),
                 RECURRENCE.replace('x>0', 'x=0'),
                 RECURRENCE.replace('x>0', 'x=-1'),
                 BETA.replace('a>0,b>0', 'a>0,b>=0'),
                 BETA.replace('a>0,b>0', 'a>0,b=0'),
                 SCALED.replace('a>0,r>0', 'a>0'),
                 SCALED.replace('a>0,r>0', 'a>0,r=0'),
                 SCALED.replace('a>0,r>0', 'a=0,r>0')]
        for text in cases:
            with self.subTest(text=text), tempfile.TemporaryDirectory() as directory, \
                 patch('special_function_agent.real_numeric.diagnose', return_value={'diagnostic': 'backend_unavailable'}), \
                 patch('special_function_agent.real_special._run_lean') as lean:
                result = verify(request(text), Path(directory) / 'run')
                self.assertEqual(result['status'], 'needs_conditions', result)
                self.assertFalse(result['full_function_proof'])
                self.assertTrue(result['pending_domain_conditions'])
                lean.assert_not_called()

    def test_positive_beta_domain_reaches_the_full_lean_checker(self):
        with tempfile.TemporaryDirectory() as directory, \
             patch('special_function_agent.real_numeric.diagnose', return_value={'diagnostic': 'backend_unavailable'}), \
             patch('special_function_agent.real_special._run_lean', return_value={'accepted': False, 'reason': 'test_stop'}) as lean:
            result = verify(request(BETA), Path(directory) / 'run')
            self.assertEqual(result['status'], 'unresolved', result)
            lean.assert_called_once()

    def test_numeric_agreement_never_replaces_a_lean_certificate(self):
        with tempfile.TemporaryDirectory() as directory, \
             patch('special_function_agent.real_numeric.diagnose', return_value={'diagnostic': 'no_mismatch_found', 'checked_samples': 9}), \
             patch('special_function_agent.real_special._run_lean', return_value={'accepted': False, 'reason': 'lean_rejected'}):
            output = Path(directory) / 'run'
            result = verify(request(), output)
            self.assertEqual(result['status'], 'unresolved')
            self.assertFalse(result['full_function_proof'])
            self.assertFalse((output / 'certificate.lean').exists())

    def test_generated_candidate_keeps_fixed_target(self):
        for route in ('direct', 'steps'):
            target = parse_identity(RECURRENCE)
            original = copy.deepcopy(target)
            candidate = default_proof(target, route)

            def start(command, **kwargs):
                path = Path(command[command.index('--output-last-message') + 1])
                path.write_text(json.dumps(candidate))
                self.assertIn('model_reasoning_effort="ultra"', command)
                return SimpleNamespace(returncode=0, communicate=lambda **kw: ('', ''))

            with self.subTest(route=route), tempfile.TemporaryDirectory() as directory, \
                 patch('special_function_agent.generate.shutil.which', return_value='/bin/codex'), \
                 patch('special_function_agent.generate.subprocess.Popen', side_effect=start) as ai, \
                 patch('special_function_agent.real_numeric.diagnose', return_value={'diagnostic': 'backend_unavailable'}), \
                 patch('special_function_agent.real_special._run_lean', return_value={'accepted': False, 'reason': 'test_stop'}):
                output = Path(directory) / 'run'
                generate(target, route, output, attempts=1)
                ai.assert_called_once()
                self.assertEqual(target, original)
                saved = json.loads((output / 'attempt-1' / 'verification' / 'request.json').read_text())
                self.assertEqual({k: v for k, v in saved.items() if k != 'proof'}, original)
                self.assertEqual(saved['proof'], candidate)

    def test_generated_candidate_cannot_add_assumptions(self):
        target = parse_identity(RECURRENCE)
        candidate = {'mode': 'direct', 'recipe': 'gamma_recurrence', 'assumptions': ['False']}

        def start(command, **kwargs):
            path = Path(command[command.index('--output-last-message') + 1])
            path.write_text(json.dumps(candidate))
            return SimpleNamespace(returncode=0, communicate=lambda **kw: ('', ''))

        with tempfile.TemporaryDirectory() as directory, \
             patch('special_function_agent.generate.shutil.which', return_value='/bin/codex'), \
             patch('special_function_agent.generate.subprocess.Popen', side_effect=start), \
             patch('special_function_agent.generate.verify') as checker:
            with self.assertRaises(InputError):
                generate(target, 'direct', Path(directory) / 'run', attempts=1)
            checker.assert_not_called()

    def test_altered_replay_evidence_is_rejected_before_lean(self):
        mutations = ('certificate', 'request', 'certificate_sha256', 'request_sha256',
                     'environment', 'conventions', 'certificate_kind', 'status', 'full_function_proof')
        for mutation in mutations:
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as directory, \
                 patch('special_function_agent.real_numeric.diagnose', return_value={'diagnostic': 'backend_unavailable'}):
                output = Path(directory) / 'run'
                with patch('special_function_agent.real_special._run_lean', return_value={'accepted': True, 'axioms': []}):
                    verify(request(), output)
                if mutation == 'certificate':
                    path = output / 'certificate.lean'
                    path.write_text(path.read_text() + '\n-- changed\n')
                elif mutation == 'request':
                    path = output / 'request.json'
                    saved = json.loads(path.read_text())
                    saved['assumptions'].append({'op': 'compare', 'variable': 'x', 'relation': 'lt',
                                                 'value': {'numerator': 5, 'denominator': 1}})
                    path.write_text(json.dumps(saved))
                else:
                    path = output / 'result.json'
                    saved = json.loads(path.read_text())
                    saved[mutation] = {'environment': {}, 'conventions': {},
                                       'certificate_kind': 'refutation', 'status': 'refuted',
                                       'full_function_proof': False}.get(mutation, '0' * 64)
                    path.write_text(json.dumps(saved))
                with patch('special_function_agent.real_special._run_lean') as lean:
                    with self.assertRaises(InputError):
                        replay(output)
                    lean.assert_not_called()


@unittest.skipUnless(importlib.util.find_spec('mpmath'), 'uses an existing mpmath runtime')
class SpecialFunctionNumericalTests(unittest.TestCase):
    def test_correct_formulas_and_wrong_coefficient_are_diagnostics(self):
        for recipe, text in FORMULAS.items():
            with self.subTest(recipe=recipe):
                result = diagnose(parse_identity(text))
                self.assertEqual(result['status'], 'unresolved')
                self.assertFalse(result['full_function_proof'])
                self.assertGreater(result['checked_samples'], 0, result)
                self.assertEqual(result['diagnostic'], 'no_mismatch_found', result)
        bad = diagnose(parse_identity(RECURRENCE.replace('=x*', '=2*x*')))
        self.assertEqual(bad['diagnostic'], 'counterexample_candidates')
        self.assertEqual(bad['status'], 'unresolved')


@unittest.skipUnless(RUN_LEAN, 'set SF_RUN_LEAN_TESTS=1 or BESSEL_RUN_LEAN_TESTS=1')
class SpecialFunctionLeanAcceptanceTests(unittest.TestCase):
    def assert_full_certificate(self, data, output):
        with patch('special_function_agent.real_numeric.diagnose', return_value={'diagnostic': 'backend_unavailable'}):
            result = verify(data, output, timeout=120)
        failure = {'status': result['status'], 'reason': result['reason'],
                   'attempts': [{k: str(attempt.get(k, ''))[-2500:]
                                 for k in ('reason', 'stdout', 'stderr')}
                                for attempt in result['attempts']]}
        self.assertEqual(result['status'], 'proved', failure)
        self.assertTrue(result['full_function_proof'])
        self.assertEqual(result['certificate_kind'], 'proof')
        self.assertEqual(result['numerical']['diagnostic'], 'backend_unavailable')
        self.assertTrue(result['attempts'][0]['accepted'])
        self.assertLessEqual(set(result['attempts'][0]['axioms']), ALLOWED_AXIOMS)
        self.assertEqual((output / 'certificate.lean').read_text(), render_lean(data))
        return result

    def test_all_three_formulas_in_both_direct_and_step_routes(self):
        with tempfile.TemporaryDirectory() as directory:
            for recipe, text in FORMULAS.items():
                for route in ('direct', 'steps'):
                    with self.subTest(recipe=recipe, route=route):
                        output = Path(directory) / (recipe + '-' + route)
                        self.assert_full_certificate(request(text, route), output)
            output = Path(directory) / 'beta_integral-steps'
            self.assertTrue(replay(output, timeout=120)['replayed'])

    def test_three_renamed_variables_and_unused_conditions_compile(self):
        text = ('int(0,infinity,u^(shape-1)*exp(-rate*u),u)='
                'rate^(-shape)*Gamma(shape);shape>0,rate>0,extra>2,extra<4')
        with tempfile.TemporaryDirectory() as directory:
            self.assert_full_certificate(request(text, 'steps'), Path(directory) / 'run')

    def test_scaled_integral_accepts_grouped_negative_exponent(self):
        text = SCALED.replace('exp(-r*t)', 'exp(-(r*t))')
        with tempfile.TemporaryDirectory() as directory:
            for route in ('direct', 'steps'):
                with self.subTest(route=route):
                    self.assert_full_certificate(request(text, route), Path(directory) / route)

    def test_wrong_coefficient_has_no_full_certificate(self):
        data = request(RECURRENCE.replace('=x*', '=2*x*'))
        with tempfile.TemporaryDirectory() as directory, \
             patch('special_function_agent.real_numeric.diagnose', return_value={'diagnostic': 'backend_unavailable'}):
            output = Path(directory) / 'run'
            result = verify(data, output, timeout=120)
            self.assertEqual(result['status'], 'unresolved', result)
            self.assertFalse(result['full_function_proof'])
            self.assertFalse(result['attempts'][0]['accepted'])
            self.assertFalse((output / 'certificate.lean').exists())


if __name__ == '__main__':
    unittest.main()
