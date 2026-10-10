"""General Legendre orthogonality keeps both natural degrees and every condition."""
import copy
import importlib.util
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from special_function_agent.archive import target_hash
from special_function_agent.core import InputError, NeedsConditions, verify, replay, validate_request
from special_function_agent.parser import parse_identity
from special_function_agent.real_numeric import diagnose
from special_function_agent.real_special import default_proof

ORTHOGONAL = 'int(-1,1,P_m(t)*P_n(t),t)=0; m natural,n natural,m!=n'
NORM = 'int(-1,1,P_n(t)^2,t)=2/(2*n+1); n natural'


def request(text, route='direct'):
    data = parse_identity(text)
    return {**data, 'proof': default_proof(data, route)}


class LegendreOrthogonalityBoundaryTests(unittest.TestCase):
    def test_two_natural_degrees_and_exact_comparison_are_preserved(self):
        data = request(ORTHOGONAL, 'steps')
        self.assertEqual(data['variables'], {'m': 'nat', 'n': 'nat'})
        self.assertEqual(data['assumptions'], [{'op': 'degree_compare', 'lhs': 'm', 'relation': 'ne', 'rhs': 'n'}])
        self.assertIn('m != n', data['proof']['steps'][0]['conditions'])
        for text in (ORTHOGONAL, ORTHOGONAL.replace('m!=n', 'n!=m'), ORTHOGONAL.replace('m!=n', 'm<n'),
                     ORTHOGONAL.replace('P_m(t)*P_n(t)', 'P_n(t)*P_m(t)')):
            self.assertEqual(request(text)['proof']['recipe'], 'legendre_orthogonal')

    def test_natural_real_conflicts_and_integral_degree_capture_are_rejected(self):
        for text in (ORTHOGONAL+',m real', ORTHOGONAL+',n real', ORTHOGONAL.replace('m natural', 'm real'),
                     ORTHOGONAL.replace('n natural', 'n integer'), ORTHOGONAL.replace('m natural', 'm integer'),
                     ORTHOGONAL.replace('(t)', '(m)').replace(',t)', ',m)'),
                     ORTHOGONAL.replace('m natural', 'm natural,m=-1'),
                     'int(-1,1,P_0(m)^2,m)=2; m natural'):
            with self.subTest(text=text), self.assertRaises((InputError, NeedsConditions)):
                parse_identity(text)

    def test_contradictory_degree_assumptions_cannot_create_vacuous_proofs(self):
        for conditions in ('m=n,m!=n', 'm<n,n<m', 'm<=n,m>n', 'm=0,n=0,m!=n',
                           'm>=2,n<=1,m<=n', 'm<m', 'm=n,m=0,n!=0'):
            with self.subTest(conditions=conditions), self.assertRaises(NeedsConditions):
                parse_identity(ORTHOGONAL.replace('m!=n', conditions))
        for conditions in ('m=0,n=1,m!=n', 'm<=n,n>=m', 'm=m,m!=n', 'm>n,n!=m'):
            parse_identity(ORTHOGONAL.replace('m!=n', conditions))

    def test_existing_real_m_and_inferred_derivative_meanings_survive(self):
        self.assertEqual(parse_identity('D(erf(m))=2*exp(-m^2)/sqrt(pi);m real')['lhs']['var'], 'm')
        data = parse_identity('D(H_m(x))=2*m*H_{m-1}(x);m natural,m>0,x real')
        self.assertEqual(data['lhs']['var'], 'x')
        self.assertEqual(data['variables'], {'m': 'nat', 'x': 'real'})
        for bad in ('m real', 'm natural,m>=0'):
            with self.assertRaises((InputError, NeedsConditions)):
                parse_identity('H_{m-1}(x)=H_m(x);'+bad+',x real')

    def test_prior_single_degree_saved_target_hashes_are_unchanged(self):
        root = Path(__file__).resolve().parents[1]
        # Each saved target remains canonical; compare new parser output with the
        # pre-existing fixture rather than reserializing a new expected value.
        for stem in ('hermite-h-derivative', 'legendre-parity', 'legendre-recurrence', 'laguerre-recurrence'):
            text = (root/'examples'/f'{stem}.txt').read_text()
            fixture = json.loads((root/'examples'/f'{stem}.target.json').read_text())
            self.assertEqual(target_hash(parse_identity(text)), target_hash(fixture), stem)
        changed = parse_identity(NORM.replace('P_n', 'P_m').replace('*n', '*m').replace('n natural', 'm natural'))
        self.assertNotEqual(target_hash(parse_identity(NORM)), target_hash(changed))
        unconstrained = parse_identity(ORTHOGONAL.replace(',m!=n', ''))
        self.assertNotEqual(target_hash(parse_identity(ORTHOGONAL)), target_hash(unconstrained))

    def test_target_condition_and_degree_type_injection_are_rejected(self):
        data = request(ORTHOGONAL, 'steps')
        for mutate in ('target', 'condition', 'type'):
            changed = copy.deepcopy(data)
            if mutate == 'target': changed['proof']['steps'][0]['after'] = {'op':'int','value':1}
            elif mutate == 'condition': changed['proof']['steps'][0]['conditions'].append('m = n')
            else: changed['variables']['m'] = 'int'
            with self.subTest(mutate=mutate), self.assertRaises(InputError):
                validate_request(changed)


@unittest.skipUnless(importlib.util.find_spec('mpmath'), 'Uses the existing optional mpmath runtime.')
class LegendreOrthogonalityNumericalTests(unittest.TestCase):
    def test_degree_relation_filters_samples_and_norm_includes_zero(self):
        report = diagnose(request(ORTHOGONAL))
        self.assertEqual(report['diagnostic'], 'no_mismatch_found')
        self.assertGreater(report['excluded_by_conditions'], 0)
        self.assertTrue(all(s['values']['m'] != s['values']['n'] for s in report['samples']))
        report = diagnose(request(NORM))
        self.assertEqual(report['diagnostic'], 'no_mismatch_found')
        self.assertTrue(any(float(s['values']['n']) == 0 for s in report['samples']))

    def test_wrong_norm_interval_or_missing_orthogonality_condition_has_counterexample(self):
        for text in (NORM.replace('2/(2*n+1)', '1/(2*n+1)'), NORM.replace('int(-1,1,', 'int(0,1,'),
                     ORTHOGONAL.replace(',m!=n', ''), ORTHOGONAL.replace('m!=n', 'm=n')):
            with self.subTest(text=text):
                self.assertEqual(diagnose(request(text))['diagnostic'], 'counterexample_candidates')


@unittest.skipUnless(os.environ.get('SF_RUN_LEAN_TESTS') == '1', 'Enable real general orthogonality acceptance.')
class LegendreOrthogonalityLeanTests(unittest.TestCase):
    def verify_one(self, text, route='direct', expected='proved'):
        with tempfile.TemporaryDirectory() as directory, patch('special_function_agent.real_numeric.importlib.import_module', side_effect=ImportError):
            output = Path(directory)/'run'
            result = verify(request(text, route), output, timeout=120)
            self.assertEqual(result['status'], expected, result)
            self.assertEqual(result['full_function_proof'], expected == 'proved')
            if expected == 'proved':
                self.assertTrue(replay(output, timeout=120)['replayed'])
            return result

    def test_general_orthogonality_and_norm_both_routes_replay_without_numerical_backend(self):
        for text in (ORTHOGONAL, NORM):
            for route in ('direct', 'steps'):
                with self.subTest(text=text, route=route): self.verify_one(text, route)

    def test_swapped_degrees_strict_inequality_zero_degree_and_fresh_binder(self):
        for text in (ORTHOGONAL.replace('P_m(t)*P_n(t)', 'P_n(t)*P_m(t)'),
                     ORTHOGONAL.replace('m!=n', 'm<n'), ORTHOGONAL.replace('m!=n', 'n<m'),
                     ORTHOGONAL.replace('(t)', '(b2)').replace(',t)', ',b2)'),
                     'int(-1,1,P_0(t)^2,t)=2/(2*0+1)', NORM.replace('P_n', 'P_m').replace('*n', '*m').replace('n natural', 'm natural'),
                     'P_m(-x)=(-1)^m*P_m(x);m natural,x real'):
            with self.subTest(text=text): self.verify_one(text)

    def test_equal_degrees_missing_condition_and_wrong_norm_are_unresolved_in_both_routes(self):
        for text in (ORTHOGONAL.replace(',m!=n', ''), ORTHOGONAL.replace('m!=n', 'm=n'),
                     NORM.replace('2/(2*n+1)', '1/(2*n+1)'), NORM.replace('int(-1,1,', 'int(0,1,')):
            for route in ('direct', 'steps'):
                with self.subTest(text=text, route=route): self.verify_one(text, route, 'unresolved')

    def test_changed_saved_degree_condition_is_detected(self):
        with tempfile.TemporaryDirectory() as directory, patch('special_function_agent.real_numeric.importlib.import_module', side_effect=ImportError):
            output = Path(directory)/'run'
            self.assertEqual(verify(request(ORTHOGONAL), output)['status'], 'proved')
            path = output/'request.json'; data = json.loads(path.read_text())
            data['assumptions'][0]['relation'] = 'eq'
            path.write_text(json.dumps(data))
            with self.assertRaises(InputError): replay(output)


if __name__ == '__main__':
    unittest.main()
