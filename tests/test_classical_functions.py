"""End-to-end Hermite and erf recipes, conventions, and evidence boundaries."""
import copy
from fractions import Fraction
import importlib.util
import json
import os
from pathlib import Path
import re
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from special_function_agent import archive, classical, registry
from special_function_agent.core import (
    ALLOWED_AXIOMS, InputError, NeedsConditions, render_lean, replay,
    validate_request, verify,
)
from special_function_agent.generate import generate, output_schema
from special_function_agent.parser import parse_identity
from special_function_agent.real_numeric import diagnose
from special_function_agent.real_special import default_proof, lean_expr, match_identity


H_DERIVATIVE = 'D(H_n(x))=2*n*H_{n-1}(x); n natural,n>=1,x real'
HE_DERIVATIVE = 'D(He_n(x))=n*He_{n-1}(x); n natural,n>=1,x real'
ERF_DERIVATIVE = 'D(erf(x))=2/sqrt(pi)*exp(-x^2); x real'
H_RECURRENCE = 'H_{n+1}(x)=2*x*H_n(x)-2*n*H_{n-1}(x); n natural,n>=1,x real'
GAUSSIAN = 'int(a,b,exp(-t^2),t)=sqrt(pi)/2*(erf(b)-erf(a)); a real,b real'
CASES = {
    'h_derivative': (H_DERIVATIVE, 'hermite_h_derivative'),
    'he_derivative': (HE_DERIVATIVE, 'hermite_he_derivative'),
    'h_zero': ('H_0(x)=1; x real', 'hermite_h_values'),
    'h_one': ('H_1(x)=2*x; x real', 'hermite_h_values'),
    'he_zero': ('He_0(x)=1; x real', 'hermite_he_values'),
    'he_one': ('He_1(x)=x; x real', 'hermite_he_values'),
    'h_recurrence': (H_RECURRENCE, 'hermite_h_recurrence'),
    'erf_derivative': (ERF_DERIVATIVE, 'erf_derivative'),
    'erf_zero': ('erf(0)=0', 'erf_zero'),
    'erf_odd': ('erf(-x)=-erf(x); x real', 'erf_odd'),
    'gaussian': (GAUSSIAN, 'gaussian_integral'),
}


def request(text, route='direct', reverse=False):
    target = parse_identity(text)
    if reverse:
        target['lhs'], target['rhs'] = target['rhs'], target['lhs']
    return {**target, 'proof': default_proof(target, route)}


class ClassicalBoundaryTests(unittest.TestCase):
    def test_all_registered_recipes_match_exact_endpoints_in_both_directions(self):
        self.assertEqual({recipe for _, recipe in CASES.values()}, set(classical.RECIPES))
        for name, (text, recipe) in CASES.items():
            for reverse in (False, True):
                with self.subTest(name=name, reverse=reverse):
                    data = request(text, reverse=reverse)
                    validate_request(data)
                    self.assertEqual(data['proof']['recipe'], recipe)
                    match = match_identity(data['lhs'], data['rhs'])
                    self.assertEqual(match['recipe'], recipe)
                    self.assertEqual(match['reverse'], reverse)
                    source = render_lean(data)
                    self.assertIn('SpecialFunctionProofAgent.'+match['theorem'], source)
                    self.assertNotIn('sorry', source)
                    self.assertNotIn('axiom ', source)
                    if reverse:
                        self.assertIn('.symm', source)

    def test_conventions_natural_degree_and_real_domains_reach_lean(self):
        source = render_lean(request(H_DERIVATIVE))
        self.assertIn('(v0 : ℕ)', source)
        self.assertIn('(v1 : ℝ)', source)
        self.assertIn('hermiteH', source)
        self.assertIn('(v0 : ℝ) ≥ (1 / 1 : ℝ)', source)
        self.assertIn('hermiteHe', render_lean(request(HE_DERIVATIVE)))
        for text in (ERF_DERIVATIVE, 'erf(-x)=-erf(x); x real', GAUSSIAN):
            data = request(text)
            self.assertEqual(data['assumptions'], [])
            self.assertNotIn('(h0 :', render_lean(data))

    def test_nested_derivatives_preserve_distinct_variable_bindings(self):
        target = parse_identity('D_x(D_y(x*y))=D_x(D_y(y*y)); x real,y real')
        names = {'x': 'v0', 'y': 'v1'}
        left = lean_expr(target['lhs'], names, target['variables'])
        right = lean_expr(target['rhs'], names, target['variables'])
        self.assertNotEqual(left, right)
        outer, inner = re.findall(r'fun \((\w+) : ℝ\)', left)
        self.assertNotEqual(outer, inner)
        self.assertIn(f'({outer} * {inner})', left)
        self.assertIn(f'({inner} * {inner})', right)
        self.assertIn('v1)', left)
        self.assertTrue(left.endswith('v0)'))

    def test_user_names_matching_generated_derivative_binders_are_renamed(self):
        ordinary = request('D_x(D_y(x*y))=0; x real,y real')
        named = request('D_{d2}(D_{d3}(d2*d3))=0; d2 real,d3 real')
        self.assertEqual(render_lean(named), render_lean(ordinary))

    def test_nested_integrals_and_derivatives_keep_each_binding_in_scope(self):
        for expression, renamed in (
            ('D_x(int(0,1,D_y(x*y*t),t))', 'D_x(int(0,1,D_y(x*y*d2),d2))'),
            ('int(0,1,D_x(D_y(x*y*t)),t)', 'int(0,1,D_x(D_y(x*y*d3)),d3)'),
        ):
            with self.subTest(expression=expression):
                data = request(expression+'=0; x real,y real')
                source = lean_expr(data['lhs'], {'x': 'v0', 'y': 'v1'}, data['variables'])
                outer, inner = re.findall(r'fun \((\w+) : ℝ\)', source)
                integral, = re.findall(r'∫ (\w+) in', source)
                self.assertEqual(len({outer, inner, integral}), 3)
                self.assertIn(f'(({outer} * {inner}) * {integral})', source)
                self.assertEqual(render_lean(data), render_lean(request(renamed+'=0; x real,y real')))
        for expression in ('D_x(int(0,1,x*y,x))', 'int(0,1,D_t(t*x),t)'):
            with self.subTest(collision=expression), self.assertRaises(InputError):
                parse_identity(expression+'=0; x real,y real')

    def test_wrong_coefficients_and_family_swaps_cannot_use_registered_recipes(self):
        for text in (H_DERIVATIVE, HE_DERIVATIVE, ERF_DERIVATIVE):
            data = request(text)
            data['rhs'] = {'op': 'mul', 'args': [{'op': 'int', 'value': 3}, data['rhs']]}
            with self.subTest(text=text):
                self.assertIsNone(match_identity(data['lhs'], data['rhs']))
                with self.assertRaises(InputError):
                    render_lean(data)
        swapped = request(H_DERIVATIVE)
        swapped['rhs']['args'][1]['op'] = 'hermite_he'
        self.assertIsNone(match_identity(swapped['lhs'], swapped['rhs']))
        with self.assertRaises(InputError):
            render_lean(swapped)

    def test_missing_degree_bounds_types_and_name_capture_stop_before_lean(self):
        original = request(H_DERIVATIVE)
        variants = []
        missing = copy.deepcopy(original)
        missing['assumptions'] = []
        variants.append(missing)
        wrong_type = copy.deepcopy(original)
        wrong_type['variables']['n'] = 'int'
        variants.append(wrong_type)
        bad_derivative = copy.deepcopy(original)
        bad_derivative['lhs']['var'] = 'n'
        variants.append(bad_derivative)
        capture = request(GAUSSIAN)
        capture['lhs']['var'] = 'a'
        variants.append(capture)
        for data in variants:
            with tempfile.TemporaryDirectory() as directory, patch('special_function_agent.real_special._run_lean') as lean:
                result = verify(data, Path(directory)/'run')
                self.assertNotEqual(result['status'], 'proved')
                lean.assert_not_called()
        with self.assertRaises(NeedsConditions):
            parse_identity(H_DERIVATIVE.replace('n>=1,', ''))

    def test_step_endpoints_conditions_and_reason_text_have_closed_scope(self):
        data = request(H_DERIVATIVE, 'steps')
        source = render_lean(data)
        reason = copy.deepcopy(data)
        reason['proof']['steps'][0]['reason'] = '\naxiom injected : False\n'
        self.assertEqual(render_lean(reason), source)
        for mutation in ('before', 'after', 'conditions', 'target', 'assumptions'):
            altered = copy.deepcopy(data)
            step = altered['proof']['steps'][0]
            if mutation in {'before', 'after'}:
                step[mutation] = {'op': 'int', 'value': 0}
            elif mutation == 'conditions':
                step['conditions'].append('x > 0')
            else:
                altered['proof'][mutation] = {'lhs': {'op': 'int', 'value': 0}}
            with self.subTest(mutation=mutation), self.assertRaises(InputError):
                validate_request(altered)
        target = parse_identity('H_n(x)=H_n(x); n natural,x real')
        shifted = parse_identity(H_DERIVATIVE)['rhs']['args'][1]
        forged = {**target, 'proof': {'mode': 'steps', 'steps': [
            {'before': target['lhs'], 'after': shifted, 'reason': '次数を変更する。', 'conditions': [], 'recipe': 'ring'},
            {'before': shifted, 'after': target['rhs'], 'reason': '次数を戻す。', 'conditions': [], 'recipe': 'ring'},
        ]}}
        with self.assertRaises(NeedsConditions):
            validate_request(forged)

    def test_ai_generated_plans_preserve_the_original_target(self):
        for text in (H_DERIVATIVE, ERF_DERIVATIVE):
            for route in ('direct', 'steps'):
                target = parse_identity(text)
                original = copy.deepcopy(target)
                candidate = default_proof(target, route)

                def start(command, **kwargs):
                    Path(command[command.index('--output-last-message')+1]).write_text(json.dumps(candidate))
                    self.assertIn('model_reasoning_effort="ultra"', command)
                    return SimpleNamespace(returncode=0, communicate=lambda **kw: ('', ''))

                with self.subTest(text=text, route=route), tempfile.TemporaryDirectory() as directory, \
                     patch('special_function_agent.generate.shutil.which', return_value='/bin/codex'), \
                     patch('special_function_agent.generate.subprocess.Popen', side_effect=start), \
                     patch('special_function_agent.generate.verify', return_value={'status': 'unresolved'}) as checker:
                    generate(target, route, Path(directory)/'run', attempts=1)
                    checked = checker.call_args.args[0]
                    self.assertEqual({k: v for k, v in checked.items() if k != 'proof'}, original)
                    self.assertEqual(target, original)
                    schema = output_schema(route, target)
                    self.assertFalse(schema['additionalProperties'])
                    self.assertNotIn('assumptions', schema['properties'])
                    self.assertNotIn('target', schema['properties'])

    def test_ai_target_and_assumption_injection_is_rejected_before_verification(self):
        target = parse_identity(H_DERIVATIVE)
        for field, value in (('assumptions', []), ('lhs', {'op': 'int', 'value': 0}),
                             ('variables', {'n': 'real', 'x': 'real'})):
            candidate = {**default_proof(target), field: value}

            def start(command, **kwargs):
                Path(command[command.index('--output-last-message')+1]).write_text(json.dumps(candidate))
                return SimpleNamespace(returncode=0, communicate=lambda **kw: ('', ''))

            with self.subTest(field=field), tempfile.TemporaryDirectory() as directory, \
                 patch('special_function_agent.generate.shutil.which', return_value='/bin/codex'), \
                 patch('special_function_agent.generate.subprocess.Popen', side_effect=start), \
                 patch('special_function_agent.generate.verify') as checker:
                with self.assertRaises(InputError):
                    generate(target, 'direct', Path(directory)/'run', attempts=1)
                checker.assert_not_called()

    def test_classical_hash_tracks_convention_degree_type_and_conditions(self):
        physical = parse_identity('H_0(x)=1; x real')
        probabilistic = parse_identity('He_0(x)=1; x real')
        self.assertNotEqual(archive.target_hash(physical), archive.target_hash(probabilistic))
        self.assertEqual(archive.canonical_target(physical)['conventions']['version'], 2)
        self.assertEqual(registry.FAMILIES['hermite_h']['definition'].split(',')[0], 'physicists H_n')
        self.assertIn('probabilists', registry.FAMILIES['hermite_he']['definition'])
        natural = parse_identity('erf(n)=erf(n); n natural')
        integer = parse_identity('erf(n)=erf(n); n integer')
        self.assertNotEqual(archive.target_hash(natural), archive.target_hash(integer))
        self.assertNotEqual(archive.target_hash(parse_identity(H_DERIVATIVE)),
                            archive.target_hash(parse_identity(H_DERIVATIVE.replace('n>=1', 'n>=2'))))
        changed = copy.deepcopy(registry.FAMILIES)
        changed['hermite_h']['definition'] = 'different Hermite normalization'
        with patch.object(registry, 'FAMILIES', changed):
            changed_key = archive.target_hash(physical)
        self.assertNotEqual(changed_key, archive.target_hash(physical))

    def test_existing_gamma_hash_preserves_version_one_conventions(self):
        # Recorded using the publicly distributed 4132d71 Gamma implementation.
        target = parse_identity('Gamma(x+1)=x*Gamma(x); x>0')
        self.assertEqual(archive.canonical_target(target)['conventions']['version'], 1)
        self.assertEqual(archive.target_hash(target), '2866593a408219281c10dc996ea6b6ac4afd9a9f9d1bf69658f2d92a1213795e')

    def test_replay_rejects_changed_request_certificate_and_conventions(self):
        for mutation in ('request', 'certificate', 'conventions'):
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as directory:
                output = Path(directory)/'run'
                with patch('special_function_agent.real_special._run_lean', return_value={'accepted': True, 'axioms': []}), \
                     patch('special_function_agent.real_numeric.diagnose', return_value={'diagnostic': 'backend_unavailable'}):
                    verify(request(H_DERIVATIVE), output)
                if mutation == 'certificate':
                    path = output/'certificate.lean'
                    path.write_text(path.read_text()+'\n-- changed certificate\n')
                else:
                    path = output/('request.json' if mutation == 'request' else 'result.json')
                    data = json.loads(path.read_text())
                    if mutation == 'request':
                        data['assumptions'][0]['value']['numerator'] = 2
                    else:
                        data['conventions']['families']['hermite_h']['definition'] = 'probabilists'
                    path.write_text(json.dumps(data))
                with patch('special_function_agent.real_special._run_lean') as lean:
                    with self.assertRaises(InputError):
                        replay(output, timeout=120)
                    lean.assert_not_called()


@unittest.skipUnless(importlib.util.find_spec('mpmath'), 'uses the existing mpmath runtime')
class ClassicalNumericalTests(unittest.TestCase):
    def test_natural_and_all_real_sampling_agree_with_the_classical_formulas(self):
        for text in (H_DERIVATIVE, HE_DERIVATIVE, ERF_DERIVATIVE, GAUSSIAN):
            with self.subTest(text=text):
                result = diagnose(request(text))
                self.assertEqual(result['diagnostic'], 'no_mismatch_found', result)
                self.assertFalse(result['full_function_proof'])
                self.assertGreater(result['checked_samples'], 0)
                if 'H_' in text or 'He_' in text:
                    degrees = [Fraction(sample['values']['n']) for sample in result['samples']]
                    self.assertTrue(all(n >= 1 and n.denominator == 1 for n in degrees))
                elif text == ERF_DERIVATIVE:
                    self.assertEqual({Fraction(sample['values']['x']) for sample in result['samples']}, {-1, 0, 1})
        natural = diagnose(request('H_n(x)=H_n(x); n natural,x real'))
        self.assertEqual({Fraction(sample['values']['n']) for sample in natural['samples']}, {0, 1, 2})

    def test_wrong_coefficient_and_convention_swap_produce_diagnostic_candidates(self):
        for text in (H_DERIVATIVE.replace('=2*n*', '=n*'),
                     ERF_DERIVATIVE.replace('=2/', '=1/'),
                     'H_1(x)=He_1(x); x real'):
            with self.subTest(text=text):
                result = diagnose(request(text))
                self.assertEqual(result['diagnostic'], 'counterexample_candidates', result)
                self.assertEqual(result['status'], 'unresolved')
                self.assertFalse(result['full_function_proof'])
                self.assertTrue(result['candidates'])


@unittest.skipUnless(os.environ.get('SF_RUN_LEAN_TESTS') == '1', 'Enable real classical Lean acceptance.')
class ClassicalLeanTests(unittest.TestCase):
    def assert_proved(self, data, output):
        result = verify(data, output, timeout=120)
        self.assertEqual(result['status'], 'proved', result)
        self.assertTrue(result['full_function_proof'])
        self.assertTrue(set(result['attempts'][-1]['axioms']) <= ALLOWED_AXIOMS)
        self.assertTrue((output/'certificate.lean').is_file())
        self.assertEqual(json.loads((output/'request.json').read_text()), data)
        return result

    def test_required_derivatives_direct_steps_and_replay(self):
        for text in (H_DERIVATIVE, ERF_DERIVATIVE):
            for route in ('direct', 'steps'):
                with self.subTest(text=text, route=route), tempfile.TemporaryDirectory() as directory, \
                     patch('special_function_agent.real_numeric.diagnose', return_value={'diagnostic': 'backend_unavailable'}):
                    output = Path(directory)/'run'
                    self.assert_proved(request(text, route), output)
                    self.assertTrue(replay(output, timeout=120)['replayed'])

    def test_natural_degree_comparisons_use_discrete_domain(self):
        for comparison in ('n>0', 'n>=1/2', 'n>=0,n!=0'):
            text = H_DERIVATIVE.replace('n>=1', comparison)
            with self.subTest(comparison=comparison), tempfile.TemporaryDirectory() as directory, \
                 patch('special_function_agent.real_numeric.diagnose', return_value={'diagnostic': 'backend_unavailable'}):
                self.assert_proved(request(text), Path(directory)/'run')

    def test_other_registered_values_recurrence_oddness_and_oriented_integrals(self):
        selected = {name: text for name, (text, _) in CASES.items()
                    if name not in {'h_derivative', 'erf_derivative', 'gaussian'}}
        selected['gaussian_forward'] = 'int(-2,3,exp(-t^2),t)=sqrt(pi)/2*(erf(3)-erf(-2))'
        selected['gaussian_backward'] = 'int(3,-2,exp(-t^2),t)=sqrt(pi)/2*(erf(-2)-erf(3))'
        selected['gaussian_real_endpoints'] = GAUSSIAN
        for name, text in selected.items():
            with self.subTest(name=name), tempfile.TemporaryDirectory() as directory, \
                 patch('special_function_agent.real_numeric.diagnose', return_value={'diagnostic': 'backend_unavailable'}):
                self.assert_proved(request(text, reverse=name == 'gaussian_backward'), Path(directory)/'run')

    def test_new_family_archives_replay_when_mpmath_is_unavailable(self):
        for text in (H_DERIVATIVE, ERF_DERIVATIVE):
            with self.subTest(text=text), tempfile.TemporaryDirectory() as directory, \
                 patch('special_function_agent.real_numeric.importlib.import_module', side_effect=ImportError):
                base = Path(directory)
                result = self.assert_proved(request(text), base/'run')
                self.assertEqual(result['numerical']['diagnostic'], 'backend_unavailable')
                record = archive.register_verification(base/'run', base/'archive', timeout=120)
                self.assertTrue(archive.replay_record(record['id'], base/'archive', timeout=120)['replayed'])
                self.assertEqual(record['canonical_target']['conventions']['version'], 2)

    def test_incorrect_classical_coefficients_remain_unresolved_after_lean(self):
        for text in (H_DERIVATIVE.replace('=2*n*', '=n*'), ERF_DERIVATIVE.replace('=2/', '=1/')):
            with self.subTest(text=text), tempfile.TemporaryDirectory() as directory, \
                 patch('special_function_agent.real_numeric.diagnose', return_value={'diagnostic': 'backend_unavailable'}):
                output = Path(directory)/'run'
                result = verify(request(text), output, timeout=120)
                self.assertEqual(result['status'], 'unresolved', result)
                self.assertFalse(result['full_function_proof'])
                self.assertFalse(result['attempts'][-1]['accepted'])
                self.assertFalse((output/'certificate.lean').exists())

    def test_nested_derivative_capture_cannot_certify_a_false_equality(self):
        text = 'D_x(D_y(x*y))=D_x(D_y(y*y)); x real,y real'
        for route in ('direct', 'steps'):
            with self.subTest(route=route), tempfile.TemporaryDirectory() as directory, \
                 patch('special_function_agent.real_numeric.diagnose', return_value={'diagnostic': 'backend_unavailable'}):
                output = Path(directory)/'run'
                result = verify(request(text, route), output, timeout=120)
                self.assertEqual(result['status'], 'unresolved', result)
                self.assertFalse(result['full_function_proof'])
                self.assertFalse(result['attempts'][-1]['accepted'])
                self.assertFalse((output/'certificate.lean').exists())


if __name__ == '__main__':
    unittest.main()
