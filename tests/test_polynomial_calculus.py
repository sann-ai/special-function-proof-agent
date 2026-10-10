"""Recurrence coefficients, adjacent orthogonality, and fixed Lean targets."""
import copy
from fractions import Fraction
import importlib.util
import os
from pathlib import Path
import re
import tempfile
import unittest
from unittest.mock import patch

from special_function_agent.core import (
    ALLOWED_AXIOMS, InputError, NeedsConditions, render_lean, replay, validate_request, verify,
)
from special_function_agent.parser import parse_identity
from special_function_agent.real_numeric import diagnose
from special_function_agent.real_special import default_proof, lean_expr, match_identity


LEGENDRE = ('(n+1)*P_{n+1}(x)=(2*n+1)*x*P_n(x)-n*P_{n-1}(x); '
            'n natural,n>=1,x real')
ADJACENT = 'int(-1,1,P_n(t)*P_{n+1}(t),t)=0; n natural'
LAGUERRE = ('(n+1)*Laguerre(n+1,a,x)=(2*n+a+1-x)*Laguerre(n,a,x)'
            '-(n+a)*Laguerre(n-1,a,x); n natural,n>=1,a real,x real')
CASES = (
    (LEGENDRE, 'legendre_recurrence', 'legendreP_recurrence'),
    (ADJACENT, 'legendre_adjacent_integral', 'legendreP_adjacent_integral'),
    (LAGUERRE, 'laguerre_recurrence', 'laguerreL_recurrence'),
)
WRONG = (
    (LEGENDRE.replace('(2*n+1)', '(3*n+1)'), 'legendre_recurrence'),
    (LAGUERRE.replace('-(n+a)*', '-(n+a+1)*'), 'laguerre_recurrence'),
    (LAGUERRE.replace('Laguerre(n-1,a,x)', 'Laguerre(n,a,x)'), 'laguerre_recurrence'),
    (ADJACENT.replace('P_{n+1}(t)', 'P_n(t)'), 'legendre_adjacent_integral'),
    (ADJACENT.replace('int(-1,1,', 'int(-1,2,'), 'legendre_adjacent_integral'),
    (ADJACENT.replace('int(-1,1,', 'int(0,1,'), 'legendre_adjacent_integral'),
    (ADJACENT.replace('P_{n+1}(t)', 'P_{n+1}(x)')+',x real', 'legendre_adjacent_integral'),
)


def request(text, route='direct', reverse=False):
    target = parse_identity(text)
    if reverse:
        target['lhs'], target['rhs'] = target['rhs'], target['lhs']
    return {**target, 'proof': default_proof(target, route)}


class PolynomialCalculusBoundaryTests(unittest.TestCase):
    def test_three_formulas_select_the_fixed_theorems_in_both_routes_and_directions(self):
        for text, recipe, theorem in CASES:
            for route in ('direct', 'steps'):
                for reverse in (False, True):
                    with self.subTest(recipe=recipe, route=route, reverse=reverse):
                        data = request(text, route, reverse)
                        validate_request(data)
                        matched = match_identity(data['lhs'], data['rhs'])
                        self.assertEqual(matched['recipe'], recipe)
                        self.assertEqual(matched['reverse'], reverse)
                        source = render_lean(data)
                        self.assertIn('SpecialFunctionProofAgent.'+theorem, source)
                        self.assertNotIn('sorry', source)
                        self.assertNotIn('axiom ', source)

    def test_positive_recurrence_degree_is_required_but_adjacent_degree_can_be_zero(self):
        for text in (LEGENDRE, LAGUERRE):
            for conditions in ('n natural', 'n natural,n>=0', 'n natural,n=0'):
                invalid = text.replace('n natural,n>=1', conditions)
                with self.subTest(text=invalid), self.assertRaises((InputError, NeedsConditions)):
                    parse_identity(invalid)
            original = request(text)
            missing = copy.deepcopy(original)
            missing['assumptions'] = []
            with self.assertRaises((InputError, NeedsConditions)):
                validate_request(missing)
            self.assertIn('(by omega)', render_lean(request(text.replace('n>=1', 'n>0'))))
        zero = request('int(-1,1,P_0(t)*P_1(t),t)=0')
        self.assertEqual(zero['variables'], {})
        self.assertEqual(zero['proof']['recipe'], 'legendre_adjacent_integral')
        self.assertEqual(request(ADJACENT)['assumptions'], [])

    def test_altered_coefficients_indices_endpoints_and_free_arguments_cannot_use_the_recipes(self):
        for text, recipe in WRONG:
            with self.subTest(text=text):
                data = request(text)
                self.assertIsNone(match_identity(data['lhs'], data['rhs']))
                data['proof'] = {'mode': 'direct', 'recipe': recipe}
                with self.assertRaises(InputError):
                    render_lean(data)

    def test_integral_binders_and_free_recurrence_arguments_keep_their_meaning(self):
        data = request(ADJACENT)
        self.assertEqual(data['variables'], {'n': 'nat'})
        source = lean_expr(data['lhs'], {'n': 'v0'}, data['variables'])
        bound, = re.findall(r'∫ (\w+) in', source)
        self.assertIn('legendreP v0 '+bound, source)
        self.assertIn('legendreP (v0 + (1 : ℕ)) '+bound, source)
        renamed = request(ADJACENT.replace('(t)', '(b0)').replace(',t)', ',b0)'))
        self.assertEqual(render_lean(data), render_lean(renamed))
        free = LEGENDRE.replace('(x)', '(y+z)').replace('*x*', '*(y+z)*').replace('x real', 'y real,z real')
        self.assertEqual(request(free)['proof']['recipe'], 'legendre_recurrence')
        dependent = LAGUERRE.split(';')[0].replace(',a,', ',x,').replace('+a', '+x')
        dependent += '; n natural,n>=1,x real'
        matched = match_identity(request(dependent)['lhs'], request(dependent)['rhs'])
        self.assertEqual(matched['arguments'][1], matched['arguments'][2])


@unittest.skipUnless(importlib.util.find_spec('mpmath'), 'Uses the existing optional mpmath runtime.')
class PolynomialCalculusNumericalTests(unittest.TestCase):
    def test_recurrences_and_adjacent_integral_include_negative_parameter_and_zero_degree_samples(self):
        for text in (LEGENDRE, ADJACENT, LAGUERRE,
                     LAGUERRE.replace('a real', 'a=-1'), LAGUERRE.replace('a real', 'a=-2')):
            with self.subTest(text=text):
                result = diagnose(request(text))
                self.assertEqual(result['diagnostic'], 'no_mismatch_found', result)
                self.assertGreater(result['checked_samples'], 0)
                self.assertFalse(result['full_function_proof'])
                if text == ADJACENT:
                    self.assertIn(0, [Fraction(sample['values']['n']) for sample in result['samples']])

    def test_false_coefficients_squared_norm_and_nonsymmetric_intervals_have_mismatch_candidates(self):
        for text, _ in WRONG:
            with self.subTest(text=text):
                result = diagnose(request(text))
                self.assertEqual(result['diagnostic'], 'counterexample_candidates', result)
                self.assertTrue(result['candidates'])


@unittest.skipUnless(os.environ.get('SF_RUN_LEAN_TESTS') == '1', 'Enable real polynomial calculus acceptance.')
class PolynomialCalculusLeanTests(unittest.TestCase):
    def assert_proved(self, data, output):
        result = verify(data, output, timeout=120)
        self.assertEqual(result['status'], 'proved', result)
        self.assertTrue(result['full_function_proof'])
        self.assertTrue(set(result['attempts'][-1]['axioms']) <= ALLOWED_AXIOMS)
        self.assertEqual(result['numerical']['diagnostic'], 'backend_unavailable')
        return result

    def test_all_three_formulas_direct_steps_and_replay_without_mpmath(self):
        for text, recipe, _ in CASES:
            for route in ('direct', 'steps'):
                with self.subTest(recipe=recipe, route=route), tempfile.TemporaryDirectory() as directory, \
                     patch('special_function_agent.real_numeric.importlib.import_module', side_effect=ImportError):
                    output = Path(directory)/'run'
                    self.assert_proved(request(text, route), output)
                    self.assertTrue(replay(output, timeout=120)['replayed'])

    def test_positive_natural_bounds_free_arguments_and_negative_laguerre_parameters(self):
        free = LEGENDRE.replace('(x)', '(y+z)').replace('*x*', '*(y+z)*').replace('x real', 'y real,z real')
        dependent = LAGUERRE.split(';')[0].replace(',a,', ',x,').replace('+a', '+x')
        dependent += '; n natural,n>0,x real'
        negative = LAGUERRE.split(';')[0].replace(',a,', ',-2,').replace('+a', '+-2')
        negative += '; n natural,n>=1,x real'
        for text in (free.replace('n>=1', 'n>0'), dependent, negative,
                     'int(-1,1,P_0(t)*P_1(t),t)=0'):
            with self.subTest(text=text), tempfile.TemporaryDirectory() as directory, \
                 patch('special_function_agent.real_numeric.importlib.import_module', side_effect=ImportError):
                self.assert_proved(request(text), Path(directory)/'run')

    def test_false_formulas_preserve_the_target_and_remain_unresolved(self):
        for text, _ in WRONG:
            with self.subTest(text=text), tempfile.TemporaryDirectory() as directory, \
                 patch('special_function_agent.real_numeric.importlib.import_module', side_effect=ImportError):
                output = Path(directory)/'run'
                result = verify(request(text), output, timeout=120)
                self.assertEqual(result['status'], 'unresolved', result)
                self.assertFalse(result['full_function_proof'])
                self.assertFalse(result['attempts'][-1]['accepted'])
                self.assertFalse((output/'certificate.lean').exists())


if __name__ == '__main__':
    unittest.main()
