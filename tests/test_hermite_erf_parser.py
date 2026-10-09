"""Hermite conventions, natural orders, and scoped real erf input."""
import copy
from fractions import Fraction
import json
from pathlib import Path
import unittest

from special_function_agent.core import InputError, NeedsConditions, validate_request
from special_function_agent.parser import parse_identity
from special_function_agent.real_bessel import (
    _validate_expr, display, domains, domain_obligations, validate_order_domains,
)


H_DERIVATIVE = 'D(H_n(x))=2*n*H_{n-1}(x); n natural,n>=1,x real'
HE_DERIVATIVE = 'D_x(He_n(x))=n*He_{n-1}(x); n natural,n>=1,x real'
ERF_DERIVATIVE = 'D(erf(x))=2/sqrt(pi)*exp(-x^2); x real'
GAUSSIAN = 'int(a,b,exp(-t^2),t)=sqrt(pi)/2*(erf(b)-erf(a)); a real,b real'


class HermiteErfParserTests(unittest.TestCase):
    def test_physical_and_probabilistic_hermite_have_separate_nodes(self):
        physical = parse_identity('H_n(x)=H(n,x); n natural,x real')
        probabilistic = parse_identity('He_n(x)=He(n,x); n natural,x real')
        self.assertEqual(physical['lhs'], physical['rhs'])
        self.assertEqual(probabilistic['lhs'], probabilistic['rhs'])
        self.assertEqual(physical['lhs']['op'], 'hermite_h')
        self.assertEqual(probabilistic['lhs']['op'], 'hermite_he')
        self.assertNotEqual(physical['lhs'], probabilistic['lhs'])
        self.assertEqual(physical['variables'], {'n': 'nat', 'x': 'real'})

    def test_natural_declarations_plain_tex_and_unicode_agree(self):
        expected = parse_identity(H_DERIVATIVE)
        for declaration in ('n in N', r'n\in\mathbb{N}', 'n∈ℕ', 'nは自然数'):
            with self.subTest(declaration=declaration):
                self.assertEqual(expected, parse_identity(H_DERIVATIVE.replace('n natural', declaration)))
        with self.assertRaises(InputError):
            parse_identity(H_DERIVATIVE+',n integer')

    def test_derivative_names_are_explicit_or_unambiguous(self):
        expected = parse_identity(H_DERIVATIVE)
        for left in ('D_x(H_n(x))', 'D_{x}(H_n(x))', 'Dx(H_n(x))', "H_n'(x)"):
            with self.subTest(left=left):
                self.assertEqual(expected, parse_identity(H_DERIVATIVE.replace('D(H_n(x))', left)))
        named = parse_identity('D_rate2(erf(rate2))=2/sqrt(pi)*exp(-rate2^2); rate2 real')
        self.assertEqual(named['lhs']['var'], 'rate2')
        inferred = parse_identity('D(erf(rate2))=2/sqrt(pi)*exp(-rate2^2); rate2 real')
        self.assertEqual(named, inferred)
        self.assertEqual(parse_identity(ERF_DERIVATIVE)['lhs']['var'], 'x')
        for text in ('D(erf(0))=0; x real', 'D(erf(x+y))=0; x real,y real'):
            with self.subTest(text=text), self.assertRaises(NeedsConditions):
                parse_identity(text)
        constant = parse_identity('D_x(erf(0))=0; x real')
        self.assertEqual(constant['variables'], {'x': 'real'})

    def test_natural_order_subtraction_requires_stated_lower_domain(self):
        for conditions in ('n natural,x real', 'n natural,n>=0,x real'):
            with self.subTest(conditions=conditions), self.assertRaises(NeedsConditions):
                parse_identity('H_{n-1}(x)=H_{n-1}(x)', conditions)
        for conditions in ('n natural,n>=1,x real', 'n natural,n>0,x real',
                           'n natural,n>=0,n!=0,x real', 'n natural,n>=1/2,x real'):
            with self.subTest(conditions=conditions):
                target = parse_identity('H_{n-1}(x)=H_{n-1}(x)', conditions)
                self.assertEqual(domains(target)['n'][0], (Fraction(1), False))
        target = parse_identity('He_{n-3}(x)=He_{n-3}(x); n natural,n>2,x real')
        self.assertEqual(domains(target)['n'][0], (Fraction(3), False))
        with self.assertRaises(NeedsConditions):
            parse_identity('He_{n-3}(x)=He_{n-3}(x); n natural,n>=2,x real')

    def test_natural_domains_include_zero_and_check_integer_consistency(self):
        target = parse_identity('H_n(x)=H_n(x); n natural,x real')
        self.assertEqual(target['assumptions'], [])
        self.assertEqual(domains(target)['n'][0], (Fraction(0), False))
        for condition in ('n<0', 'n=-1', '0<n<1', 'n=1/2', 'n<=0,n!=0'):
            with self.subTest(condition=condition), self.assertRaises(NeedsConditions):
                parse_identity('H_n(x)=H_n(x); n natural,x real,'+condition)

    def test_bessel_integer_and_hermite_natural_order_types_stay_separate(self):
        integer = parse_identity('Y_n(x)=Y_n(x); n integer,x>0')
        self.assertEqual(integer['variables']['n'], 'int')
        for text in ('H_n(x)=H_n(x); n integer,x real',
                     'He_n(x)=He_n(x); n integer,x real',
                     'Y_n(x)=Y_n(x); n natural,x>0',
                     'H_n(x)=J_n(x); n natural,x>0'):
            with self.subTest(text=text), self.assertRaises(InputError):
                parse_identity(text)
        for text in ('H_n(x)=H_n(x); x real', 'He_n(x)=He_n(x); x real'):
            with self.subTest(text=text), self.assertRaises(NeedsConditions):
                parse_identity(text)
        forged = copy.deepcopy(integer)
        forged['variables']['n'] = 'nat'
        with self.assertRaises(InputError):
            validate_request(forged, require_proof=False)

    def test_natural_order_grammar_is_closed(self):
        for order in ('0', '1', '12', 'n', 'n+2', 'n-2'):
            parse_identity(f'H_{{{order}}}(x)=H_{{{order}}}(x); n natural,n>=2,x real')
        for order in ('-1', '1/2', '-n', 'n+n', '2*n', 'n+13', 'n+(-1)', 'n+(n+1)'):
            with self.subTest(order=order), self.assertRaises(InputError):
                parse_identity(f'H_{{{order}}}(x)=0; n natural,n>=20,x real')
        literal = parse_identity('H_0(x)=1; x real')
        for value in (True, 1.0, -1, 1001):
            forged = copy.deepcopy(literal)
            forged['lhs']['order']['value'] = value
            with self.subTest(value=value), self.assertRaises(InputError):
                validate_request(forged, require_proof=False)

    def test_domain_helper_covers_proposed_step_orders(self):
        target = parse_identity('H_n(x)=H_n(x); n natural,x real')
        endpoint = parse_identity('H_{n-1}(x)=H_{n-1}(x); n natural,n>=1,x real')['lhs']
        _validate_expr(endpoint, target['variables'])
        with self.assertRaises(NeedsConditions):
            validate_order_domains([endpoint], domains(target))
        positive = parse_identity(H_DERIVATIVE)
        validate_order_domains([endpoint], domains(positive))

    def test_erf_all_real_inputs_keep_empty_assumptions(self):
        for text in (ERF_DERIVATIVE, 'erf(-x)=-erf(x); x real', GAUSSIAN):
            target = parse_identity(text)
            self.assertEqual(target['assumptions'], [])
            self.assertEqual(domain_obligations(target, None), [])
        zero = parse_identity('erf(0)=0')
        self.assertEqual(zero['variables'], {})
        self.assertEqual(zero['assumptions'], [])
        self.assertEqual(zero['lhs'], {'op': 'erf', 'arg': {'op': 'int', 'value': 0}})
        for condition in ('x<0', 'x=0'):
            target = parse_identity('erf(-x)=-erf(x); '+condition)
            self.assertEqual(len(target['assumptions']), 1)

    def test_pi_sqrt_and_tex_erf_derivative_agree(self):
        tex = r'D_x(\operatorname{erf}(x))=\frac{2}{\sqrt{\pi}}\exp(-x^2); x\in\mathbb{R}'
        self.assertEqual(parse_identity(ERF_DERIVATIVE), parse_identity(tex))
        target = parse_identity(ERF_DERIVATIVE)
        self.assertEqual(target['rhs']['args'][0]['args'][1], {'op': 'sqrt', 'arg': {'op': 'pi'}})
        forged = copy.deepcopy(target)
        forged['rhs']['args'][0]['args'][1]['arg']['value'] = 3
        with self.assertRaises(InputError):
            validate_request(forged, require_proof=False)

    def test_finite_gaussian_keeps_bounds_and_integral_scope(self):
        target = parse_identity(GAUSSIAN)
        self.assertEqual(target['variables'], {'a': 'real', 'b': 'real'})
        self.assertEqual(target['lhs']['var'], 't')
        self.assertEqual(target['lhs']['lower'], {'op': 'var', 'name': 'a'})
        self.assertEqual(target['lhs']['upper'], {'op': 'var', 'name': 'b'})
        tex = r'\int_a^b\exp(-t^2)\,dt=\sqrt{\pi}/2*(\operatorname{erf}(b)-\operatorname{erf}(a)); a real,b real'
        self.assertEqual(target, parse_identity(tex))

    def test_derivative_and_integral_name_collisions_are_rejected(self):
        for text in ('D_n(erf(x))=0; n natural,x real',
                     'D_0(erf(x))=0; x real',
                     'int(0,1,D_t(erf(t)),t)=0; x real',
                     'D_x(int(0,1,erf(x),x))=0; x real',
                     'int(0,1,erf(t),pi)=0; x real'):
            with self.subTest(text=text), self.assertRaises(InputError):
                parse_identity(text)
        target = parse_identity(ERF_DERIVATIVE)
        for value in ('missing', 'n', 'pi', {'name': 'x'}, True):
            forged = copy.deepcopy(target)
            forged['lhs']['var'] = value
            with self.subTest(value=value), self.assertRaises(InputError):
                validate_request(forged, require_proof=False)

    def test_new_constants_and_function_names_are_reserved(self):
        target = parse_identity(ERF_DERIVATIVE)
        for name in ('pi', 'H', 'He', 'erf'):
            forged = copy.deepcopy(target)
            forged['variables'][name] = 'real'
            with self.subTest(name=name), self.assertRaises(InputError):
                validate_request(forged, require_proof=False)
        target = parse_identity('D_position1(erf(position1+offset_2))=erf(scale3); position1 real,offset_2 real,scale3 real')
        self.assertEqual(len(target['variables']), 3)
        with self.assertRaises(InputError):
            parse_identity('D_x(erf(x+a+b+c))=0; x real,a real,b real,c real')

    def test_display_roundtrip_and_saved_examples(self):
        for text in (H_DERIVATIVE, HE_DERIVATIVE, ERF_DERIVATIVE, GAUSSIAN):
            target = parse_identity(text)
            equation = display(target['lhs'])+'='+display(target['rhs'])
            self.assertEqual(target, parse_identity(equation, text.split(';')[1]))
        examples = Path(__file__).resolve().parents[1]/'examples'
        names = ('hermite-h-derivative', 'hermite-he-derivative', 'hermite-h-zero', 'hermite-h-one',
                 'hermite-he-zero', 'hermite-he-one', 'erf-derivative', 'erf-zero', 'erf-odd',
                 'gaussian-finite-integral')
        for name in names:
            with self.subTest(name=name):
                target = json.loads((examples/(name+'.target.json')).read_text())
                self.assertEqual(target, parse_identity((examples/(name+'.txt')).read_text()))


if __name__ == '__main__':
    unittest.main()
