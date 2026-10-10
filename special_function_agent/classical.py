"""Structural Hermite/erf identities under explicit degree conventions."""
from .core import InputError

RECIPES = ('hermite_h_derivative', 'hermite_he_derivative', 'hermite_h_values',
           'hermite_he_values', 'hermite_h_recurrence', 'erf_derivative',
           'erf_zero', 'erf_odd', 'gaussian_integral')
REASONS = {
    'hermite_h_derivative': '物理学規約Hの定義と確率論規約Heとの変換から導いた微分公式を、明示した自然数次数の条件で適用する。',
    'hermite_he_derivative': '確率論規約Heの多項式の微分公式を、明示した自然数次数の条件で適用する。',
    'hermite_h_values': '物理学規約Hの定義から低次数の多項式を評価する。',
    'hermite_he_values': '確率論規約Heの定義から低次数の多項式を評価する。',
    'hermite_h_recurrence': '物理学規約Hと確率論規約Heを結ぶ変換から導いた漸化式を適用する。',
    'erf_derivative': '誤差関数のGaussian積分による定義に微積分の基本定理を適用する。',
    'erf_zero': '誤差関数の定義で、端点がともに0の積分を評価する。',
    'erf_odd': 'Gaussianの偶関数性と積分方向の反転から誤差関数の奇関数性を適用する。',
    'gaussian_integral': '誤差関数の微分公式と微積分の基本定理から、指定された実端点のGaussian積分を評価する。',
}


def integer(value): return {'op': 'int', 'value': value}
def binary(op, a, b): return {'op': op, 'args': [a, b]}
def neg(arg): return {'op': 'neg', 'arg': arg}
def erf(arg): return {'op': 'erf', 'arg': arg}
def hermite(op, n, x): return {'op': op, 'order': n, 'arg': x}
def gaussian(x): return {'op': 'exp', 'arg': neg({'op': 'pow', 'base': x, 'exponent': 2})}
def sqrt_pi(): return {'op': 'sqrt', 'arg': {'op': 'pi'}}

def predecessor(n):
    if n.get('op') == 'int': return integer(n['value'] - 1)
    if n.get('op') == 'add' and n['args'][1].get('op') == 'int' and n['args'][1]['value'] >= 1:
        offset = n['args'][1]['value'] - 1
        return n['args'][0] if offset == 0 else binary('add', n['args'][0], integer(offset))
    return binary('sub', n, integer(1))


def match(lhs, rhs):
    for left, right, reverse in ((lhs, rhs, False), (rhs, lhs, True)):
        found = None
        if left.get('op') == 'deriv':
            arg, x = left['arg'], {'op': 'var', 'name': left['var']}
            if arg.get('op') in {'hermite_h', 'hermite_he'} and arg['arg'] == x:
                family, n = arg['op'], arg['order']
                coefficient = binary('mul', integer(2), n) if family == 'hermite_h' else n
                expected = binary('mul', coefficient, hermite(family, predecessor(n), x))
                if right == expected:
                    found = {'recipe': family + '_derivative',
                             'theorem': 'hermiteH_derivative' if family == 'hermite_h' else 'hermiteHe_derivative',
                             'arguments': [n, x], 'natural_arguments': [0], 'positive_degree': n}
            if arg == erf(x):
                numerator = binary('mul', integer(2), gaussian(x))
                if right in [binary('div', numerator, sqrt_pi()), binary('mul', binary('div', integer(2), sqrt_pi()), gaussian(x))]:
                    found = {'recipe': 'erf_derivative', 'theorem': 'deriv_erf', 'arguments': [x]}
        if left.get('op') in {'hermite_h', 'hermite_he'}:
            family, n, x = left['op'], left['order'], left['arg']
            prefix = 'hermiteH' if family == 'hermite_h' else 'hermiteHe'
            if n == integer(0) and right == integer(1):
                found = {'recipe': family + '_values', 'theorem': prefix+'_zero', 'arguments': [x]}
            if n == integer(1) and right == (binary('mul', integer(2), x) if family == 'hermite_h' else x):
                found = {'recipe': family + '_values', 'theorem': prefix+'_one', 'arguments': [x]}
            if family == 'hermite_h' and n.get('op') == 'add' and n['args'][1] == integer(1):
                degree = n['args'][0]
                expected = binary('sub', binary('mul', binary('mul', integer(2), x), hermite(family, degree, x)),
                                  binary('mul', binary('mul', integer(2), degree), hermite(family, binary('sub', degree, integer(1)), x)))
                if right == expected:
                    found = {'recipe': 'hermite_h_recurrence', 'theorem': 'hermiteH_recurrence',
                             'arguments': [degree, x], 'natural_arguments': [0], 'positive_degree': degree}
        if left == erf(integer(0)) and right == integer(0):
            found = {'recipe': 'erf_zero', 'theorem': 'erf_zero', 'arguments': []}
        if left.get('op') == 'erf' and left['arg'].get('op') == 'neg':
            x = left['arg']['arg']
            if right == neg(erf(x)):
                found = {'recipe': 'erf_odd', 'theorem': 'erf_neg', 'arguments': [x]}
        if left.get('op') == 'integral' and left['upper'].get('op') != 'infinity':
            t = {'op': 'var', 'name': left['var']}
            a, b = left['lower'], left['upper']
            expected = binary('mul', binary('div', sqrt_pi(), integer(2)), binary('sub', erf(b), erf(a)))
            if left['body'] == gaussian(t) and right == expected:
                found = {'recipe': 'gaussian_integral', 'theorem': 'gaussian_integral', 'arguments': [a, b]}
        if found:
            return {**found, 'reverse': reverse}
    return None


def lean_natural(node, names):
    if node['op'] == 'int' and node['value'] >= 0:
        return f'({node["value"]} : ℕ)'
    if node['op'] == 'var' and node['name'] in {'m', 'n'}:
        return names[node['name']]
    if node['op'] in {'add', 'sub'}:
        return '(' + lean_natural(node['args'][0], names) + (' + ' if node['op'] == 'add' else ' - ') + lean_natural(node['args'][1], names) + ')'
    raise InputError('Use the supported natural Hermite degree.')


def proof_lines(matched, names, expression, *, definition_context=False):
    naturals = matched.get('natural_arguments', [])
    args = ' '.join(lean_natural(a, names) if i in naturals else expression(a) for i, a in enumerate(matched['arguments']))
    if 'positive_degree' in matched:
        args += ' (by omega)'
    fact = 'SpecialFunctionProofAgent.' + matched['theorem'] + (' ' + args if args else '')
    if matched['reverse']: fact = f'({fact}).symm'
    # normalize only notation and multiplication association, retaining the fixed target
    # New definition expansions may already have normalized notation. Keep the
    # historical renderer stable for existing saved certificates.
    simplify = 'simp only [neg_mul, Real.rpow_eq_pow]'
    if definition_context:
        simplify = '(try '+simplify+')'
    return [f'convert ({fact}) using 1 <;> ({simplify} <;> ring)']
