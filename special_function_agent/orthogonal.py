"""Closed identities for the standard real Legendre, Laguerre and Jacobi families."""
from .classical import integer, binary, neg, predecessor, lean_natural

RECIPES = ('legendre_values', 'legendre_parity', 'legendre_endpoints',
           'legendre_recurrence', 'legendre_adjacent_integral',
           'laguerre_values', 'laguerre_recurrence', 'laguerre_derivative', 'jacobi_values',
           'jacobi_derivative', 'jacobi_legendre')
REASONS = {
    'legendre_values': 'shifted Legendreとの変換と有限和から標準Legendreの低次数を評価する。',
    'legendre_parity': '標準Legendreとshifted Legendreの変換から、自然数次数の鏡映公式を適用する。',
    'legendre_endpoints': '標準Legendreの有限和と鏡映公式から指定された端点の値を評価する。',
    'legendre_recurrence': '標準Legendreの有限和の係数比較から証明した三項漸化式を、元の自然数次数条件で適用する。',
    'legendre_adjacent_integral': '隣接次数のLegendre積は奇関数であり、連続性と対称区間の積分から積分値0を得る。',
    'laguerre_recurrence': '一般化Laguerreの有限和の係数比較から証明した三項漸化式を、自然数次数と実パラメータを保持して適用する。',
    'laguerre_values': '一般化Laguerreの標準有限和から低次数を評価する。',
    'laguerre_derivative': '一般化Laguerreの有限和を微分し、次数を1下げてパラメータを1上げる公式を適用する。',
    'jacobi_values': 'Jacobiの標準有限和から、元の実パラメータを保持して低次数を評価する。',
    'jacobi_derivative': 'Jacobiの有限和の微分公式により、次数を1下げて両パラメータを1上げる。',
    'jacobi_legendre': 'Jacobiの両パラメータが0の有限和を標準Legendreの定義へ接続する。',
}


def polynomial(op, n, x, a=None, b=None):
    return {'op': op, 'order': n, 'arg': x, **({'alpha': a} if a is not None else {}),
            **({'beta': b} if b is not None else {})}


def shift(a, amount):
    return integer(a['value']+amount) if a['op'] == 'int' else binary('add', a, integer(amount))

def parity(n):
    return {'op': 'pow', 'base': integer(-1), 'exponent': n['value']} if n['op'] == 'int' else {
        'op': 'rpow', 'base': integer(-1), 'exponent': n}


def match(lhs, rhs):
    for left, right, reverse in ((lhs, rhs, False), (rhs, lhs, True)):
        found = None
        op = left.get('op')
        if op == 'mul':
            coefficient, fn = left['args']
            if fn.get('op') == 'legendre':
                n, x = predecessor(fn['order']), fn['arg']
                expected = binary('sub', binary('mul', binary('mul',
                    binary('add', binary('mul', integer(2), n), integer(1)), x),
                    polynomial('legendre', n, x)),
                    binary('mul', n, polynomial('legendre', predecessor(n), x)))
                if coefficient == binary('add', n, integer(1)) and right == expected:
                    found = {'recipe': 'legendre_recurrence', 'theorem': 'legendreP_recurrence',
                             'arguments': [n, x], 'natural_arguments': [0], 'positive_degree': n}
            if fn.get('op') == 'laguerre':
                n, x, a = predecessor(fn['order']), fn['arg'], fn['alpha']
                expected = binary('sub', binary('mul', binary('sub', binary('add',
                    binary('add', binary('mul', integer(2), n), a), integer(1)), x),
                    polynomial('laguerre', n, x, a)),
                    binary('mul', binary('add', n, a), polynomial('laguerre', predecessor(n), x, a)))
                if coefficient == binary('add', n, integer(1)) and right == expected:
                    found = {'recipe': 'laguerre_recurrence', 'theorem': 'laguerreL_recurrence',
                             'arguments': [n, a, x], 'natural_arguments': [0], 'positive_degree': n}
        if op == 'integral' and left['lower'] == integer(-1) and left['upper'] == integer(1):
            body, t = left['body'], {'op': 'var', 'name': left['var']}
            if body.get('op') == 'mul':
                first, second = body['args']
                if first.get('op') == 'legendre' and first['arg'] == t:
                    n = first['order']
                    if second == polynomial('legendre', shift(n, 1), t) and right == integer(0):
                        found = {'recipe': 'legendre_adjacent_integral', 'theorem': 'legendreP_adjacent_integral',
                                 'arguments': [n], 'natural_arguments': [0]}
        if op == 'legendre':
            n, x = left['order'], left['arg']
            common = {'arguments': [n, x], 'natural_arguments': [0]}
            if x.get('op') == 'neg' and right == binary('mul', parity(n), polynomial(op, n, x['arg'])):
                found = {**common, 'arguments': [n, x['arg']], 'recipe': 'legendre_parity', 'theorem': 'legendreP_neg'}
            elif x == integer(1) and right == integer(1):
                found = {'arguments': [n], 'natural_arguments': [0], 'recipe': 'legendre_endpoints', 'theorem': 'legendreP_at_one'}
            elif x == integer(-1) and right == parity(n):
                found = {'arguments': [n], 'natural_arguments': [0], 'recipe': 'legendre_endpoints', 'theorem': 'legendreP_at_neg_one'}
            values = [integer(1), x, binary('div', binary('sub', binary('mul', integer(3), {'op': 'pow', 'base': x, 'exponent': 2}), integer(1)), integer(2))]
            for k, value in enumerate(values):
                if n == integer(k) and right == value:
                    found = {'recipe': 'legendre_values', 'theorem': 'legendreP_'+('zero','one','two')[k], 'arguments': [x]}
        if op in {'laguerre', 'jacobi'}:
            n, x, a = left['order'], left['arg'], left['alpha']
            b = left.get('beta')
            value = binary('sub', binary('add', a, integer(1)), x) if op == 'laguerre' else binary('div',
                binary('add', binary('sub', a, b), binary('mul', binary('add', binary('add', a, b), integer(2)), x)), integer(2))
            if op == 'laguerre':
                second = binary('div', binary('add', binary('sub', {'op': 'pow', 'base': x, 'exponent': 2},
                    binary('mul', binary('mul', integer(2), binary('add', a, integer(2))), x)),
                    binary('mul', binary('add', a, integer(1)), binary('add', a, integer(2)))), integer(2))
            else:
                s3 = binary('add', binary('add', a, b), integer(3))
                s4 = binary('add', binary('add', a, b), integer(4))
                z = binary('div', binary('sub', x, integer(1)), integer(2))
                second = binary('add', binary('add', binary('div', binary('mul', binary('add', a, integer(1)), binary('add', a, integer(2))), integer(2)),
                    binary('mul', binary('mul', s3, binary('add', a, integer(2))), z)),
                    binary('mul', binary('div', binary('mul', s3, s4), integer(2)), {'op': 'pow', 'base': z, 'exponent': 2}))
            for k, expected in enumerate((integer(1), value, second)):
                if n == integer(k) and right == expected:
                    found = {'recipe': op+'_values', 'theorem': ('laguerreL' if op == 'laguerre' else 'jacobiP')+('_zero', '_one', '_two')[k],
                             'arguments': [a, x] if op == 'laguerre' else [a, b, x]}
            if op == 'laguerre' and a == integer(0):
                ordinary = [integer(1), binary('sub', integer(1), x),
                    binary('div', binary('add', binary('sub', {'op': 'pow', 'base': x, 'exponent': 2}, binary('mul', integer(4), x)), integer(2)), integer(2))]
                for k, expected in enumerate(ordinary):
                    if n == integer(k) and right == expected:
                        found = {'recipe': 'laguerre_values', 'theorem': 'laguerreL'+('_zero','_one','_two')[k], 'arguments': [a,x]}
            if op == 'jacobi' and a == integer(0) and b == integer(0) and right == polynomial('legendre', n, x):
                found = {'recipe': 'jacobi_legendre', 'theorem': 'jacobiP_zero_zero', 'arguments': [n, x], 'natural_arguments': [0]}
        if op == 'deriv':
            fn = left['arg']
            x = {'op': 'var', 'name': left['var']}
            family = fn.get('op')
            if family in {'laguerre', 'jacobi'} and fn['arg'] == x:
                n, a = fn['order'], fn['alpha']
                shifted_a = shift(a, 1)
                args = [n, a, x]
                expected = neg(polynomial(family, predecessor(n), x, shifted_a))
                if family == 'jacobi':
                    b = fn['beta']
                    args = [n, a, b, x]
                    coefficient = binary('div', binary('add', binary('add', binary('add', n, a), b), integer(1)), integer(2))
                    expected = binary('mul', coefficient, polynomial(family, predecessor(n), x, shifted_a, shift(b, 1)))
                if right == expected:
                    found = {'recipe': family+'_derivative', 'theorem': ('laguerreL' if family == 'laguerre' else 'jacobiP')+'_derivative',
                             'arguments': args, 'natural_arguments': [0], 'positive_degree': n}
        if found:
            return {**found, 'reverse': reverse}
    return None


def proof_lines(matched, names, expression):
    args = ' '.join(lean_natural(a, names) if i in matched.get('natural_arguments', []) else expression(a)
                    for i, a in enumerate(matched['arguments']))
    if 'positive_degree' in matched:
        args += ' (by omega)'
    fact = 'SpecialFunctionProofAgent.' + matched['theorem'] + (' '+args if args else '')
    if matched['reverse']: fact = f'({fact}).symm'
    return [f'convert ({fact}) using 1 <;> ((try simp only [neg_mul, Real.rpow_eq_pow, Real.rpow_natCast, Nat.cast_add, Nat.cast_one]) <;> ring)']
