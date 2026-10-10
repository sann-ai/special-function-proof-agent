"""Explicit conditional certificates for the standard integer-Y construction."""
from .classical import binary, integer


def match(data):
    """Retain the legacy Y target while exposing its two analytic obligations."""
    n = {'op': 'var', 'name': 'n'}
    if data['variables'].get('n') != 'int':
        return None
    for left, right, reverse in ((data['lhs'], data['rhs'], False),
                                 (data['rhs'], data['lhs'], True)):
        if left.get('op') != 'add':
            continue
        first, second = left['args']
        if first.get('op') != 'bessel_y' or second.get('op') != 'bessel_y':
            continue
        x = first['arg']
        if x.get('op') != 'var' or data['variables'].get(x['name']) != 'real':
            continue
        y = lambda order: {'op': 'bessel_y', 'order': order, 'arg': x}
        expected = binary('mul', binary('div', binary('mul', integer(2), n), x), y(n))
        if (first == y(binary('sub', n, integer(1))) and
                second == y(binary('add', n, integer(1))) and right == expected):
            return {
                'id': 'integer_y_recurrence', 'reverse': reverse,
                'scope': 'integer_y_recurrence_under_explicit_order_differentiability',
                'substitutions': {'n': 'n', 'x': x['name']},
                'assumptions': ['0 < x',
                    'DifferentiableAt ℝ (fun a : ℝ => realBesselJ a x) 0',
                    'DifferentiableAt ℝ (fun a : ℝ => realBesselJ a x) 1'],
                'steps': [
                    '正の引数xを固定し、Jの次数0と1での次数微分可能性を明示前提とする。',
                    'Jの漸化式から次数微分可能性を全整数点へ伝播させる。',
                    'Jの漸化式を次数で微分し、標準次数微分式で定義したbesselYIntの漸化式へ接続する。',
                    '同じ2前提から非整数Yの整数次数への極限とbesselYIntの一致を得る。'],
                'sources': ['https://dlmf.nist.gov/10.2.E4', 'https://dlmf.nist.gov/10.6.E1'],
                'formal_obligations': [
                    '正の引数でJの次数0における次数微分可能性を証明すること。',
                    '正の引数でJの次数1における次数微分可能性を証明すること。'],
            }
    return None


def conditional_source(template):
    left = ('SpecialFunctionProofAgent.besselYInt (n - 1) x + '
            'SpecialFunctionProofAgent.besselYInt (n + 1) x')
    right = '(2 * (n : ℝ) / x) * SpecialFunctionProofAgent.besselYInt n x'
    if template['reverse']:
        left, right = right, left
    fact = ('SpecialFunctionProofAgent.besselYInt_recurrence_of_order_differentiable_zero_one '
            'n x hx h0 h1')
    if template['reverse']:
        fact = '(' + fact + ').symm'
    return ('import SpecialFunctionProofAgent.BesselYInteger\n\n'
            'namespace BesselAgentCandidate\n\n'
            'theorem target (n : ℤ) (x : ℝ) (hx : 0 < x)\n'
            '    (h0 : DifferentiableAt ℝ (fun a : ℝ => SpecialFunctionProofAgent.realBesselJ a x) 0)\n'
            '    (h1 : DifferentiableAt ℝ (fun a : ℝ => SpecialFunctionProofAgent.realBesselJ a x) 1) :\n'
            f'    {left} = {right} := by\n  exact {fact}\n\n'
            'end BesselAgentCandidate\n\n'
            '#eval IO.println "BESSEL_AUDIT_BEGIN"\n'
            '#print axioms BesselAgentCandidate.target\n'
            '#eval IO.println "BESSEL_AUDIT_END"\n')
