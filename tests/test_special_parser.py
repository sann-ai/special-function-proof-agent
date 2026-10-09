"""Closed v2 special-function syntax, free variables, and integral scopes."""
import copy
import json
from pathlib import Path
import unittest

from special_function_agent.core import InputError, NeedsConditions, validate_request
from special_function_agent.parser import parse_identity
from special_function_agent.real_bessel import display, domain_obligations


GAMMA = 'Gamma(x+1)=x*Gamma(x); x>0'
BETA = 'int(0,1,t^(a-1)*(1-t)^(b-1),t)=Gamma(a)*Gamma(b)/Gamma(a+b); a>0,b>0'
SCALED = 'int(0,infinity,t^(a-1)*exp(-r*t),t)=r^(-a)*Gamma(a); a>0,r>0'


class SpecialParserTests(unittest.TestCase):
    def test_plain_tex_and_infinity_forms_agree(self):
        pairs = [
            (GAMMA, r'\Gamma(x+1)=x\Gamma(x); x>0'),
            (BETA, r'\int_0^1 t^{a-1}(1-t)^{b-1}\,dt=\frac{\Gamma(a)\Gamma(b)}{\Gamma(a+b)}; a>0,b>0'),
            (SCALED, r'\int_0^{\infty}t^{a-1}\exp(-r*t)\,dt=r^{-a}\Gamma(a); a>0,r>0'),
            (SCALED, SCALED.replace('infinity', '∞')),
            (SCALED, SCALED.replace('infinity', 'inf')),
        ]
        for plain, tex in pairs:
            with self.subTest(tex=tex):
                self.assertEqual(parse_identity(plain), parse_identity(tex))

    def test_arbitrary_safe_names_and_bound_variable_are_preserved(self):
        text = 'int(0,infinity,q^(alpha_1-1)*exp(-rate2*q),q)=rate2^(-alpha_1)*Gamma(alpha_1); alpha_1>0,rate2>0'
        data = parse_identity(text)
        self.assertEqual(data['variables'], {'alpha_1': 'real', 'rate2': 'real'})
        self.assertEqual(data['lhs']['var'], 'q')
        self.assertEqual(data['lhs']['upper'], {'op': 'infinity'})
        self.assertEqual(data['rhs']['args'][0]['op'], 'rpow')

    def test_three_free_reals_plus_integer_and_bound_name(self):
        data = parse_identity('int(0,1,Gamma(a+b+c+n)*t,t)=Gamma(a); a>0,b>0,c>0,n integer')
        self.assertEqual(data['variables'], {'a': 'real', 'b': 'real', 'c': 'real', 'n': 'int'})
        with self.assertRaises(InputError):
            parse_identity('Gamma(a+b+c+e)=Gamma(a); a>0,b>0,c>0,e>0')
        with self.assertRaises(NeedsConditions):
            parse_identity('Gamma(a+n)=Gamma(a); a>0')

    def test_conditions_are_preserved_without_added_positivity(self):
        data = parse_identity('Gamma(a+1)=a*Gamma(a); a real')
        self.assertEqual(data['assumptions'], [])
        self.assertEqual(data['variables'], {'a': 'real'})
        data = parse_identity('Gamma(a)/Gamma(b)=Gamma(a)/Gamma(b); a real,b real,Gamma(b)!=0')
        self.assertEqual(len(data['assumptions']), 1)
        self.assertEqual(data['assumptions'][0]['relation'], 'ne')
        self.assertEqual(domain_obligations(data, None), [])
        pending = parse_identity('Gamma(a)/Gamma(b)=Gamma(a)/Gamma(b); a real,b real')
        self.assertEqual(domain_obligations(pending, None), ['Gamma(b) != 0'])
        self.assertEqual(domain_obligations(parse_identity(BETA), None), [])

    def test_general_denominator_and_function_zero_assumptions(self):
        data = parse_identity('Gamma(a)/(a-b)=Gamma(b); a>0,b>0,a-b!=0,Gamma(a-1)=0')
        self.assertEqual([atom['op'] for atom in data['assumptions']],
                         ['compare', 'compare', 'expr_compare', 'expr_compare'])
        self.assertEqual(domain_obligations(data, None), [])
        with self.assertRaises(NeedsConditions):
            parse_identity('Gamma(a)=Gamma(a); a>0,Gamma(a)=0,Gamma(a)!=0')
        with self.assertRaises(NeedsConditions):
            parse_identity('Gamma(a)=Gamma(a); a>0,a<=0')

    def test_invalid_names_types_and_undeclared_variables_are_rejected(self):
        original = parse_identity(GAMMA)
        for variables in [{'x': 'complex'}, {'x': 'int'}, {'n': 'real'},
                          {'Gamma': 'real'}, {'x;axiom': 'real'}, {'_x': 'real'},
                          {'α': 'real'}, {'a'*33: 'real'}, {'x': True}]:
            data = copy.deepcopy(original)
            data['variables'] = variables
            with self.subTest(variables=variables), self.assertRaises(InputError):
                validate_request(data, require_proof=False)
        data = copy.deepcopy(original)
        data['lhs']['arg']['args'][0]['name'] = 'undeclared'
        with self.assertRaises(InputError):
            validate_request(data, require_proof=False)

    def test_integral_scope_and_free_name_collisions_are_rejected(self):
        invalid = [
            'int(0,1,Gamma(t),t)=Gamma(t); t>0',
            'int(0,t,Gamma(t),t)=Gamma(a); a>0',
            'int(0,1,int(0,1,Gamma(t),t),t)=Gamma(a); a>0',
            'int(0,1,Gamma(n),n)=Gamma(a); a>0,n integer',
            'int(0,1,Gamma(q),t)=Gamma(a); a>0,t>0',
        ]
        for text in invalid:
            with self.subTest(text=text), self.assertRaises(InputError):
                parse_identity(text)
        target = parse_identity('int(0,1,Gamma(t),t)=Gamma(a); a>0')
        target['lhs']['body']['arg']['name'] = 'q'
        with self.assertRaises(InputError):
            validate_request(target, require_proof=False)

    def test_infinity_is_only_an_integral_upper_endpoint(self):
        for text in ['Gamma(a)=infinity; a>0',
                     'int(infinity,1,Gamma(t),t)=Gamma(a); a>0',
                     'int(0,infinity+1,Gamma(t),t)=Gamma(a); a>0']:
            with self.subTest(text=text), self.assertRaises(InputError):
                parse_identity(text)
        target = parse_identity(SCALED)
        target['lhs']['upper']['value'] = 1
        with self.assertRaises(InputError):
            validate_request(target, require_proof=False)

    def test_closed_operation_fields_and_numeric_types(self):
        original = parse_identity(SCALED)
        mutations = [
            lambda d: d['lhs'].update(variable='t'),
            lambda d: d['rhs']['args'][0].update(exponent=2),
            lambda d: d['lhs']['lower'].update(value=True),
            lambda d: d['lhs'].update(var={'op': 'var', 'name': 't'}),
            lambda d: d['rhs']['args'][1].update(op='Gamma'),
        ]
        for mutate in mutations:
            data = copy.deepcopy(original)
            mutate(data)
            with self.assertRaises(InputError):
                validate_request(data, require_proof=False)

    def test_gamma_proof_modes_and_bessel_diagnostic_boundary(self):
        from special_function_agent.real_special import default_proof
        for text in (GAMMA, BETA, SCALED):
            target = parse_identity(text)
            for route in ('direct', 'steps', 'diagnostic'):
                proof = {'mode': 'diagnostic'} if route == 'diagnostic' else default_proof(target, route)
                validate_request({**target, 'proof': proof})
        bessel = parse_identity('Y_0(z)=Y_0(z); z>0')
        with self.assertRaises(InputError):
            validate_request({**bessel, 'proof': {'mode': 'direct', 'recipe': 'ring'}})

    def test_display_round_trip_and_saved_example_targets(self):
        for text in (GAMMA, BETA, SCALED):
            target = parse_identity(text)
            equation = display(target['lhs'])+'='+display(target['rhs'])
            self.assertEqual(parse_identity(equation, text.split(';')[1]), target)
        root = Path(__file__).resolve().parents[1] / 'examples'
        for name in ('gamma-recurrence', 'beta-integral', 'scaled-gamma-integral', 'gamma-missing-condition'):
            self.assertEqual(parse_identity((root/(name+'.txt')).read_text()),
                             json.loads((root/(name+'.target.json')).read_text()))


if __name__ == '__main__':
    unittest.main()
