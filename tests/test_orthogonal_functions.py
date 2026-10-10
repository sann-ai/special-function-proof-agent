"""Standard polynomial conventions, closed proof plans, and Lean acceptance."""
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

from special_function_agent import archive, orthogonal, registry
from special_function_agent.core import (
    ALLOWED_AXIOMS, InputError, NeedsConditions, render_lean, replay,
    validate_request, verify,
)
from special_function_agent.generate import generate, output_schema
from special_function_agent.parser import parse_identity
from special_function_agent.real_numeric import diagnose
from special_function_agent.real_special import default_proof, lean_expr, match_identity


PARITY = 'P_n(-x)=(-1)^n*P_n(x); n natural,x real'
L_DERIVATIVE = 'D_x(Laguerre(n,a,x))=-Laguerre(n-1,a+1,x); n natural,n>=1,a real,x real'
J_DERIVATIVE = ('D_x(Jacobi(n,a,b,x))=(n+a+b+1)/2*Jacobi(n-1,a+1,b+1,x); '
                'n natural,n>=1,a real,b real,x real')
BRIDGE = 'Jacobi(n,0,0,x)=P_n(x); n natural,x real'
MAIN_CASES = (PARITY, L_DERIVATIVE, J_DERIVATIVE, BRIDGE)
CASES = {
    'legendre_parity': (PARITY, 'legendre_parity'),
    'legendre_zero': ('P_0(x)=1; x real', 'legendre_values'),
    'legendre_one': ('P_1(x)=x; x real', 'legendre_values'),
    'legendre_two': ('P_2(x)=(3*x^2-1)/2; x real', 'legendre_values'),
    'legendre_right': ('P_n(1)=1; n natural', 'legendre_endpoints'),
    'legendre_left': ('P_n(-1)=(-1)^n; n natural', 'legendre_endpoints'),
    'laguerre_zero': ('Laguerre(0,a,x)=1; a real,x real', 'laguerre_values'),
    'laguerre_one': ('Laguerre(1,a,x)=a+1-x; a real,x real', 'laguerre_values'),
    'laguerre_two': ('Laguerre(2,a,x)=(x^2-2*(a+2)*x+(a+1)*(a+2))/2; a real,x real', 'laguerre_values'),
    'ordinary_laguerre_one': ('L_1(x)=1-x; x real', 'laguerre_values'),
    'ordinary_laguerre_two': ('L_2(x)=(x^2-4*x+2)/2; x real', 'laguerre_values'),
    'laguerre_derivative': (L_DERIVATIVE, 'laguerre_derivative'),
    'jacobi_zero': ('Jacobi(0,a,b,x)=1; a real,b real,x real', 'jacobi_values'),
    'jacobi_one': ('Jacobi(1,a,b,x)=((a-b)+(a+b+2)*x)/2; a real,b real,x real', 'jacobi_values'),
    'jacobi_two': ('Jacobi(2,a,b,x)=(a+1)*(a+2)/2+(a+b+3)*(a+2)*((x-1)/2)'
                   '+(a+b+3)*(a+b+4)/2*((x-1)/2)^2; a real,b real,x real', 'jacobi_values'),
    'jacobi_derivative': (J_DERIVATIVE, 'jacobi_derivative'),
    'jacobi_legendre': (BRIDGE, 'jacobi_legendre'),
}


def request(text, route='direct', reverse=False):
    target = parse_identity(text)
    if reverse:
        target['lhs'], target['rhs'] = target['rhs'], target['lhs']
    return {**target, 'proof': default_proof(target, route)}


class OrthogonalBoundaryTests(unittest.TestCase):
    def test_all_recipes_and_low_degree_normalizations_match_both_directions(self):
        self.assertLessEqual({recipe for _, recipe in CASES.values()}, set(orthogonal.RECIPES))
        for name, (text, recipe) in CASES.items():
            for reverse in (False, True):
                with self.subTest(name=name, reverse=reverse):
                    data = request(text, reverse=reverse)
                    validate_request(data)
                    self.assertEqual(data['proof']['recipe'], recipe)
                    matched = match_identity(data['lhs'], data['rhs'])
                    self.assertEqual(matched['recipe'], recipe)
                    self.assertEqual(matched['reverse'], reverse)
                    source = render_lean(data)
                    self.assertIn('SpecialFunctionProofAgent.'+matched['theorem'], source)
                    self.assertNotIn('sorry', source)
                    self.assertNotIn('axiom ', source)
                    if reverse:
                        self.assertIn('.symm', source)

    def test_notation_aliases_preserve_family_parameters_and_exact_targets(self):
        aliases = (
            ('P_n(x)', 'Legendre(n,x)', 'n natural,x real'),
            ('L_n(x)', 'Laguerre(n,0,x)', 'n natural,x real'),
            ('L_n^{(α)}(x)', 'Laguerre(n,alpha,x)', 'n natural,α real,x real'),
            (r'L_n^{(\alpha)}(x)', 'Laguerre(n,alpha,x)', r'n natural,\alpha real,x real'),
            ('P_n^{(α,β)}(x)', 'Jacobi(n,alpha,beta,x)', 'n natural,α real,β real,x real'),
            (r'P_n^{(\alpha,\beta)}(x)', 'Jacobi(n,alpha,beta,x)', r'n natural,\alpha real,\beta real,x real'),
        )
        for shorthand, explicit, conditions in aliases:
            with self.subTest(shorthand=shorthand):
                data = parse_identity(shorthand+'='+explicit+'; '+conditions)
                self.assertEqual(data['lhs'], data['rhs'])
                self.assertEqual(data['variables']['n'], 'nat')
        for text in ('P_n^2(x)=P_n(x); n natural,x real',
                     'P_n^{m}(x)=P_n(x); n natural,m real,x real'):
            with self.subTest(associated=text), self.assertRaises((InputError, NeedsConditions)):
                parse_identity(text)

    def test_all_real_parameters_and_natural_degrees_reach_the_fixed_lean_target(self):
        data = request(J_DERIVATIVE)
        self.assertEqual(data['variables'], {'a': 'real', 'b': 'real', 'n': 'nat', 'x': 'real'})
        self.assertEqual(len(data['assumptions']), 1)
        source = render_lean(data)
        self.assertIn('(v2 : ℕ)', source)
        self.assertIn('(v0 : ℝ)', source)
        self.assertIn('(v1 : ℝ)', source)
        self.assertIn('(v3 : ℝ)', source)
        for text in (PARITY, BRIDGE, CASES['laguerre_two'][0], CASES['jacobi_two'][0]):
            self.assertEqual(request(text)['assumptions'], [])
        for comparison in ('n>0', 'n>=1/2', 'n>=0,n!=0'):
            self.assertIn('jacobiP_derivative', render_lean(request(J_DERIVATIVE.replace('n>=1', comparison))))

    def test_invalid_degree_bounds_types_and_zero_denominators_stop_before_lean(self):
        for text in (L_DERIVATIVE.replace('n>=1,', ''), J_DERIVATIVE.replace('n>=1,', ''),
                     'P_{-1}(x)=1; x real', 'Laguerre(-1,0,x)=1; x real',
                     'Jacobi(n,a,b,x)=1; n integer,a real,b real,x real',
                     'Laguerre(n,1/0,x)=Laguerre(n,1/0,x); n natural,x real'):
            with self.subTest(text=text), self.assertRaises((InputError, NeedsConditions)):
                parse_identity(text)
        original = request(J_DERIVATIVE)
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
        for data in variants:
            with tempfile.TemporaryDirectory() as directory, patch('special_function_agent.real_special._run_lean') as lean:
                result = verify(data, Path(directory)/'run')
                self.assertNotEqual(result['status'], 'proved')
                lean.assert_not_called()

    def test_wrong_coefficients_parameter_shifts_and_specializations_cannot_use_theorems(self):
        cases = (
            (PARITY.replace('=(-1)^n*', '='), 'legendre_parity'),
            (L_DERIVATIVE.replace('=-Laguerre', '=-2*Laguerre'), 'laguerre_derivative'),
            (L_DERIVATIVE.replace('n-1,a+1,x', 'n-1,a,x'), 'laguerre_derivative'),
            (J_DERIVATIVE.replace('(n+a+b+1)/2', '(n+a+b+2)/2'), 'jacobi_derivative'),
            (J_DERIVATIVE.replace('n-1,a+1,b+1,x', 'n-1,a,b+1,x'), 'jacobi_derivative'),
            (J_DERIVATIVE.replace('n-1,a+1,b+1,x', 'n-1,a+1,b,x'), 'jacobi_derivative'),
            (BRIDGE.replace('n,0,0,x', 'n,0,1,x'), 'jacobi_legendre'),
        )
        for text, recipe in cases:
            with self.subTest(text=text):
                data = request(text)
                self.assertIsNone(match_identity(data['lhs'], data['rhs']))
                data['proof'] = {'mode': 'direct', 'recipe': recipe}
                with self.assertRaises(InputError):
                    render_lean(data)

    def test_nested_derivatives_keep_polynomial_arguments_in_distinct_scopes(self):
        data = request('D_x(D_y(P_1(x*y)))=D_x(D_y(P_1(y*y))); x real,y real')
        names = {'x': 'v0', 'y': 'v1'}
        left = lean_expr(data['lhs'], names, data['variables'])
        right = lean_expr(data['rhs'], names, data['variables'])
        outer, inner = re.findall(r'fun \((\w+) : ℝ\)', left)
        self.assertNotEqual(outer, inner)
        self.assertNotEqual(left, right)
        self.assertIn(f'({outer} * {inner})', left)
        self.assertIn(f'({inner} * {inner})', right)
        renamed = request('D_{d2}(D_{d3}(P_1(d2*d3)))=D_{d2}(D_{d3}(P_1(d3*d3))); d2 real,d3 real')
        self.assertEqual(render_lean(data), render_lean(renamed))
        with self.assertRaises(InputError):
            parse_identity('int(0,1,P_n(x),x)=1; n natural,x real')

    def test_integral_binders_apply_to_polynomial_parameters_and_argument(self):
        for family, body, expected in (('laguerreL', 'Laguerre(1,t,t)', '1'),
                                       ('jacobiP', 'Jacobi(1,t,t,t)', '5/6')):
            data = request('int(0,1,'+body+',t)='+expected)
            self.assertEqual(data['variables'], {})
            source = lean_expr(data['lhs'], {}, data['variables'])
            bound, = re.findall(r'∫ (\w+) in', source)
            arguments = ' '.join([bound] * (2 if family == 'laguerreL' else 3))
            self.assertIn(f'SpecialFunctionProofAgent.{family} (1 : ℕ) {arguments}', source)
            renamed = request('int(0,1,'+body.replace('t', 'b0')+',b0)='+expected)
            self.assertEqual(render_lean(data), render_lean(renamed))

    def test_steps_cannot_replace_endpoints_or_inject_target_assumptions(self):
        original = request(J_DERIVATIVE, 'steps')
        source = render_lean(original)
        reason = copy.deepcopy(original)
        reason['proof']['steps'][0]['reason'] = '\naxiom injected : False\n'
        self.assertEqual(render_lean(reason), source)
        for mutation in ('before', 'after', 'conditions', 'target', 'assumptions'):
            data = copy.deepcopy(original)
            if mutation in {'before', 'after'}:
                data['proof']['steps'][0][mutation] = {'op': 'int', 'value': 0}
            elif mutation == 'conditions':
                data['proof']['steps'][0]['conditions'].append('a > -1')
            else:
                data['proof'][mutation] = {'lhs': {'op': 'int', 'value': 0}}
            with self.subTest(mutation=mutation), self.assertRaises(InputError):
                validate_request(data)

    def test_ai_schema_and_injected_candidates_preserve_the_fixed_target(self):
        target = parse_identity(J_DERIVATIVE)
        for route in ('direct', 'steps'):
            schema = output_schema(route, target)
            self.assertFalse(schema['additionalProperties'])
            self.assertNotIn('target', schema['properties'])
            self.assertNotIn('assumptions', schema['properties'])
            for field, value in (('assumptions', []), ('lhs', {'op': 'int', 'value': 0}),
                                 ('variables', {'n': 'nat', 'x': 'real'})):
                candidate = {**default_proof(target, route), field: value}

                def start(command, **kwargs):
                    Path(command[command.index('--output-last-message')+1]).write_text(json.dumps(candidate))
                    return SimpleNamespace(returncode=0, communicate=lambda **kw: ('', ''))

                with self.subTest(route=route, field=field), tempfile.TemporaryDirectory() as directory, \
                     patch('special_function_agent.generate.shutil.which', return_value='/bin/codex'), \
                     patch('special_function_agent.generate.subprocess.Popen', side_effect=start), \
                     patch('special_function_agent.generate.verify') as checker:
                    with self.assertRaises(InputError):
                        generate(target, route, Path(directory)/'run', attempts=1)
                    checker.assert_not_called()

    def test_new_conventions_track_parameters_and_preserve_public_classical_hashes(self):
        for text in MAIN_CASES:
            self.assertEqual(archive.canonical_target(parse_identity(text))['conventions']['version'], 3)
        first = parse_identity('Jacobi(n,0,0,x)=P_n(x); n natural,x real')
        altered = parse_identity('Jacobi(n,0,1,x)=P_n(x); n natural,x real')
        self.assertNotEqual(archive.target_hash(first), archive.target_hash(altered))
        changed = copy.deepcopy(registry.FAMILIES)
        changed['legendre']['definition'] = 'different Legendre normalization'
        with patch.object(registry, 'FAMILIES', changed):
            key = archive.target_hash(first)
        self.assertNotEqual(key, archive.target_hash(first))
        # Fixed hashes from public commit cc6e813, including its v2 conventions.
        old = (
            ('D(H_n(x))=2*n*H_{n-1}(x); n natural,n>=1,x real',
             '8938c566e6ddb6817503c905495c167d9ec072f2c43d9b269fdd49d27f2fe453'),
            ('D(He_n(x))=n*He_{n-1}(x); n natural,n>=1,x real',
             '6b04f69ce2a1295fce9b126a2a5d5b1dcfd328c9330604cd6eedb893f796c443'),
            ('D(erf(x))=2/sqrt(pi)*exp(-x^2); x real',
             'b67437a99b57718efe899535e8279e98802557d288723e4df0931ebffca59d0c'),
            ('int(a,b,exp(-t^2),t)=sqrt(pi)/2*(erf(b)-erf(a)); a real,b real',
             'd2b127b8bed78d20f483a47ffa54319c7ef3c197f0f31c725695c959f6cc84d4'),
        )
        for text, expected in old:
            with self.subTest(legacy=text):
                data = parse_identity(text)
                self.assertEqual(archive.canonical_target(data)['conventions']['version'], 2)
                self.assertEqual(archive.target_hash(data), expected)

    def test_replay_rejects_altered_fixed_evidence_before_running_lean(self):
        for mutation in ('request', 'certificate', 'conventions', 'certificate_kind', 'environment'):
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as directory:
                output = Path(directory)/'run'
                with patch('special_function_agent.real_special._run_lean', return_value={'accepted': True, 'axioms': []}), \
                     patch('special_function_agent.real_numeric.diagnose', return_value={'diagnostic': 'backend_unavailable'}):
                    verify(request(J_DERIVATIVE), output)
                if mutation == 'certificate':
                    path = output/'certificate.lean'
                    path.write_text(path.read_text()+'\n-- changed saved bytes\n')
                else:
                    path = output/('request.json' if mutation == 'request' else 'result.json')
                    data = json.loads(path.read_text())
                    if mutation == 'request':
                        data['assumptions'][0]['value']['numerator'] = 2
                    elif mutation == 'conventions':
                        data['conventions']['families']['jacobi']['definition'] = 'other normalization'
                    elif mutation == 'certificate_kind':
                        data['certificate_kind'] = 'refutation'
                    else:
                        data['environment'] = {'changed': 'foundation'}
                    path.write_text(json.dumps(data))
                with patch('special_function_agent.real_special._run_lean') as lean:
                    with self.assertRaises(InputError):
                        replay(output)
                    lean.assert_not_called()


@unittest.skipUnless(importlib.util.find_spec('mpmath'), 'Uses the existing optional mpmath runtime.')
class OrthogonalNumericalTests(unittest.TestCase):
    def test_standard_low_degrees_and_main_formulas_have_consistent_samples(self):
        for text in (*MAIN_CASES, CASES['legendre_two'][0], CASES['ordinary_laguerre_one'][0],
                     CASES['ordinary_laguerre_two'][0]):
            with self.subTest(text=text):
                result = diagnose(request(text))
                self.assertEqual(result['diagnostic'], 'no_mismatch_found', result)
                self.assertGreater(result['checked_samples'], 0)
                self.assertFalse(result['full_function_proof'])
                if 'n>=1' in text:
                    degrees = [Fraction(sample['values']['n']) for sample in result['samples']]
                    self.assertTrue(all(n >= 1 and n.denominator == 1 for n in degrees))

    def test_negative_parameter_boundaries_remain_finite(self):
        texts = (
            CASES['laguerre_two'][0].replace('a real,x real', 'a=-2,x real'),
            CASES['jacobi_two'][0].replace('a real,b real,x real', 'a=-1,b=0,x real'),
            CASES['jacobi_two'][0].replace('a real,b real,x real', 'a=-2,b=-1,x real'),
        )
        for text in texts:
            with self.subTest(text=text):
                result = diagnose(request(text))
                self.assertEqual(result['diagnostic'], 'no_mismatch_found', result)
                self.assertGreater(result['checked_samples'], 0)
                self.assertFalse(result['candidates'])

    def test_integrals_evaluate_the_bound_parameter_at_each_point(self):
        for text in ('int(0,1,Laguerre(1,t,t),t)=1',
                     'int(0,1,Jacobi(1,t,t,t),t)=5/6'):
            with self.subTest(text=text):
                result = diagnose(request(text))
                self.assertEqual(result['diagnostic'], 'no_mismatch_found', result)
                self.assertEqual(result['checked_samples'], 1)

    def test_positive_parameter_finite_sums_agree_with_existing_mpmath_functions(self):
        import mpmath as mp
        texts = (
            ('Laguerre(n,a,x)=Laguerre(n,a,x); n natural,a=1/2,x real', 'laguerre'),
            ('Jacobi(n,a,b,x)=Jacobi(n,a,b,x); n natural,a=1/2,b=1/3,x real', 'jacobi'),
        )
        for text, family in texts:
            result = diagnose(request(text))
            self.assertGreater(result['checked_samples'], 0)
            with mp.workdps(60):
                for sample in result['samples']:
                    values = {name: mp.mpf(value) for name, value in sample['values'].items()}
                    expected = (mp.laguerre(int(values['n']), values['a'], values['x']) if family == 'laguerre'
                                else mp.jacobi(int(values['n']), values['a'], values['b'], values['x']))
                    with self.subTest(family=family, values=sample['values']):
                        self.assertLess(abs(mp.mpf(sample['lhs'])-expected), mp.mpf('1e-40'))

    def test_convention_or_coefficient_errors_generate_mismatch_candidates(self):
        for text in ('P_1(x)=1-2*x; x real', 'L_1(x)=1+x; x real',
                     J_DERIVATIVE.replace('(n+a+b+1)/2', '(n+a+b+2)/2')):
            with self.subTest(text=text):
                result = diagnose(request(text))
                self.assertEqual(result['diagnostic'], 'counterexample_candidates', result)
                self.assertTrue(result['candidates'])
                self.assertFalse(result['full_function_proof'])


@unittest.skipUnless(os.environ.get('SF_RUN_LEAN_TESTS') == '1', 'Enable real orthogonal Lean acceptance.')
class OrthogonalLeanTests(unittest.TestCase):
    def assert_proved(self, data, output):
        result = verify(data, output, timeout=120)
        self.assertEqual(result['status'], 'proved', result)
        self.assertTrue(result['full_function_proof'])
        self.assertTrue(set(result['attempts'][-1]['axioms']) <= ALLOWED_AXIOMS)
        self.assertEqual(json.loads((output/'request.json').read_text()), data)
        self.assertTrue((output/'certificate.lean').is_file())
        return result

    def test_main_generic_formulas_direct_steps_and_replay(self):
        for text in MAIN_CASES:
            for route in ('direct', 'steps'):
                with self.subTest(text=text, route=route), tempfile.TemporaryDirectory() as directory, \
                     patch('special_function_agent.real_numeric.diagnose', return_value={'diagnostic': 'backend_unavailable'}):
                    output = Path(directory)/'run'
                    self.assert_proved(request(text, route), output)
                    self.assertTrue(replay(output, timeout=120)['replayed'])

    def test_all_registered_initial_values_and_endpoints(self):
        for name, (text, _) in CASES.items():
            if text in MAIN_CASES:
                continue
            with self.subTest(name=name), tempfile.TemporaryDirectory() as directory, \
                 patch('special_function_agent.real_numeric.diagnose', return_value={'diagnostic': 'backend_unavailable'}):
                self.assert_proved(request(text, reverse=name == 'legendre_two'), Path(directory)/'run')

    def test_negative_parameters_and_discrete_natural_bounds(self):
        texts = (
            'D_x(Laguerre(n,-1,x))=-Laguerre(n-1,0,x); n natural,n>=1,x real',
            'D_x(Laguerre(n,-2,x))=-Laguerre(n-1,-1,x); n natural,n>=1,x real',
            'D_x(Jacobi(n,-1,-2,x))=(n+-1+-2+1)/2*Jacobi(n-1,0,-1,x); n natural,n>=1,x real',
            L_DERIVATIVE.replace('n>=1', 'n>0'),
            J_DERIVATIVE.replace('n>=1', 'n>=1/2'),
            J_DERIVATIVE.replace('n>=1', 'n>=0,n!=0'),
        )
        for text in texts:
            with self.subTest(text=text), tempfile.TemporaryDirectory() as directory, \
                 patch('special_function_agent.real_numeric.diagnose', return_value={'diagnostic': 'backend_unavailable'}):
                self.assert_proved(request(text), Path(directory)/'run')

    def test_wrong_formulas_and_nested_capture_remain_unresolved(self):
        texts = (
            L_DERIVATIVE.replace('=-Laguerre', '=-2*Laguerre'),
            L_DERIVATIVE.replace('n-1,a+1,x', 'n-1,a,x'),
            J_DERIVATIVE.replace('n-1,a+1,b+1,x', 'n-1,a+1,b,x'),
            'D_x(D_y(P_1(x*y)))=D_x(D_y(P_1(y*y))); x real,y real',
            'D_x(Laguerre(n,x,x))=-Laguerre(n-1,x+1,x); n natural,n>=1,x real',
        )
        for text in texts:
            with self.subTest(text=text), tempfile.TemporaryDirectory() as directory, \
                 patch('special_function_agent.real_numeric.diagnose', return_value={'diagnostic': 'backend_unavailable'}):
                output = Path(directory)/'run'
                result = verify(request(text), output, timeout=120)
                self.assertEqual(result['status'], 'unresolved', result)
                self.assertFalse(result['full_function_proof'])
                self.assertFalse(result['attempts'][-1]['accepted'])
                self.assertFalse((output/'certificate.lean').exists())

    def test_argument_dependent_parameters_cannot_use_a_fixed_parameter_derivative(self):
        texts = (
            'D_x(Laguerre(1,x,x))=-1; x real',
            'D_x(Jacobi(1,x,0,x))=(1+x+0+1)/2*Jacobi(0,x+1,1,x); x real',
        )
        for text in texts:
            for route in ('direct', 'steps'):
                with self.subTest(text=text, route=route), tempfile.TemporaryDirectory() as directory, \
                     patch('special_function_agent.real_numeric.diagnose', return_value={'diagnostic': 'backend_unavailable'}):
                    output = Path(directory)/'run'
                    result = verify(request(text, route), output, timeout=120)
                    self.assertEqual(result['status'], 'unresolved', result)
                    self.assertFalse(result['full_function_proof'])
                    self.assertFalse(result['attempts'][-1]['accepted'])
                    self.assertFalse((output/'certificate.lean').exists())

    def test_archive_replays_the_fixed_polynomial_target_without_mpmath(self):
        with tempfile.TemporaryDirectory() as directory, \
             patch('special_function_agent.real_numeric.importlib.import_module', side_effect=ImportError):
            base = Path(directory)
            result = self.assert_proved(request(BRIDGE), base/'run')
            self.assertEqual(result['numerical']['diagnostic'], 'backend_unavailable')
            record = archive.register_verification(base/'run', base/'archive', timeout=120)
            self.assertEqual(record['canonical_target']['conventions']['version'], 3)
            self.assertTrue(archive.replay_record(record['id'], base/'archive', timeout=120)['replayed'])


if __name__ == '__main__':
    unittest.main()
