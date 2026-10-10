"""The fixed root fraction, including both denominators proved nonzero."""
from .classical import binary, integer

RECIPES = ('cross_product_root',)
FORMAL_SCOPE = 'standard positive-axis Bessel cross root identity with proved positive energy and nonzero denominators'
REASONS = {'cross_product_root':
           '元の根条件と0<λ<1、z>0から標準J・Yの漸化式とWronskianを適用する。正エネルギー積分で左分母の正値性と右分母の非零性を証明し、元の分数等式へ接続する。'}


def cross(n, m, s, t):
    return {'op': 'bessel_cross', 'orders': [integer(n), integer(m)], 'args': [s, t]}


def match_identity(lhs, rhs):
    from .real_bessel import _walk
    for left, right, reverse in ((lhs, rhs, False), (rhs, lhs, True)):
        for node in _walk(left):
            if node.get('op') != 'bessel_cross' or node.get('orders') != [integer(0), integer(0)]:
                continue
            z, scaled = node['args']
            if z.get('op') != 'var' or scaled.get('op') != 'mul':
                continue
            lam, same_z = scaled['args']
            if lam.get('op') != 'var' or lam == z or same_z != z:
                continue
            a, b, c, q = (cross(0, 0, z, scaled), cross(1, 1, z, scaled),
                           cross(0, 2, z, scaled), cross(0, 1, z, z))
            left_expected = binary('div', {'op': 'pow', 'base': a, 'exponent': 2},
                binary('add', {'op': 'pow', 'base': q, 'exponent': 2},
                       binary('mul', binary('mul', {'op': 'pow', 'base': lam, 'exponent': 2}, a), c)))
            denominator = binary('sub', b, binary('mul', lam, a))
            fraction = binary('div', integer(1), lam)
            right_expected = (binary('div', binary('mul', fraction, a), denominator),
                              binary('mul', fraction, binary('div', a, denominator)))
            if left == left_expected and right in right_expected:
                return {'recipe': RECIPES[0], 'theorem': 'besselCross_root_identity',
                        'arguments': [z, lam], 'reverse': reverse}
    return None


def complete_target(data):
    matched = match_identity(data.get('lhs'), data.get('rhs'))
    if not matched or any(data['variables'].get(v['name']) != 'real' for v in matched['arguments']):
        return False
    from .real_bessel import domains, _positive
    z, lam = matched['arguments']
    bounds = domains(data)
    hi = bounds[lam['name']][1]
    root = {'op': 'expr_compare', 'lhs': cross(0, 1, z, binary('mul', lam, z)),
            'relation': 'eq', 'rhs': integer(0)}
    return (_positive(z, bounds) and _positive(lam, bounds)
            and hi is not None and (hi[0] < 1 or hi == (1, True))
            and root in data['assumptions'])


def proof_lines(matched, names, expression):
    z, lam = matched['arguments']
    zlean, llean = expression(z), expression(lam)
    root = expression(cross(0, 1, z, binary('mul', lam, z)))
    args = f'{zlean} {llean} (by linarith) (by linarith) (by linarith) h_cross_root'
    fact = f'SpecialFunctionProofAgent.besselCross_root_identity {args}'
    if matched['reverse']:
        fact = f'({fact}).symm'
    return [
        f'have h_cross_root : SpecialFunctionProofAgent.besselCross 0 1 {zlean} ({llean} * {zlean}) = 0 := by',
        '  simpa only [SpecialFunctionProofAgent.besselCross, Int.cast_zero, Int.cast_one] using',
        f'    (show {root} = 0 from by assumption)',
        f'have h_left_denominator_pos := SpecialFunctionProofAgent.besselCross_root_left_denominator_pos {args}',
        'have h_left_denominator_ne_zero := ne_of_gt h_left_denominator_pos',
        f'have h_right_denominator_ne_zero := SpecialFunctionProofAgent.besselCross_root_right_denominator_ne_zero {args}',
        f'convert ({fact}) using 1 <;> norm_num [SpecialFunctionProofAgent.besselCross] <;> ring',
    ]
