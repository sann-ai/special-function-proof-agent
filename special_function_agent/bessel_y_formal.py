"""Full positive-axis Y certificates for a closed half-integer scope."""
from .classical import binary, integer

FORMAL_SCOPE = 'positive-axis Y at fixed orders -1/2, 1/2, 3/2'
RECIPES = ('bessel_y_half_recurrence', 'bessel_y_half_derivative')
REASONS = {
    'bessel_y_half_recurrence': '非整数次数YのJによる標準接続から証明した漸化式を、半整数次数と正の実引数に適用する。',
    'bessel_y_half_derivative': '非整数次数Yの標準接続とJの微分から、半整数Yの対称微分公式を適用する。',
}


def y(order, x):
    return {'op': 'bessel_y_noninteger', 'order': {'op': 'rational', 'numerator': order, 'denominator': 2}, 'arg': x}


def contains(data):
    from .real_bessel import _walk
    return any(n.get('op') == 'bessel_y_noninteger' for n in _walk([data.get('lhs'), data.get('rhs'), data.get('assumptions', [])]))


def match(lhs, rhs):
    from .real_bessel import _walk
    for left, right, reverse in ((lhs, rhs, False), (rhs, lhs, True)):
        arguments = [n['arg'] for n in _walk(left) if n.get('op') == 'bessel_y_noninteger']
        for x in arguments:
            if x.get('op') != 'var': continue
            low, mid, high = y(-1, x), y(1, x), y(3, x)
            if left == binary('add', low, high) and right == binary('div', mid, x):
                return {'recipe': RECIPES[0], 'theorem': 'Yhalf_recurrence', 'arguments': [x], 'reverse': reverse}
            if left == {'op': 'deriv', 'var': x['name'], 'arg': mid} and right == binary('div', binary('sub', low, high), integer(2)):
                return {'recipe': RECIPES[1], 'theorem': 'Yhalf_derivative', 'arguments': [x], 'reverse': reverse}
    return None


def proof_lines(matched, names, expression):
    fact = 'SpecialFunctionProofAgent.'+matched['theorem']+' '+expression(matched['arguments'][0])+' (by linarith)'
    if matched['reverse']: fact = f'({fact}).symm'
    return [f'convert ({fact}) using 1 <;> norm_num <;> ring']
