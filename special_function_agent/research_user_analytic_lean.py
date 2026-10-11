"""Verifier-owned bridges for user expressions in three bounded analytic classes."""
from copy import deepcopy
import json

from .core import _sha
from . import research_user_analytic as syntax

OPS = {'series_definition', 'integral_definition', 'ode_definition'}
NS = 'SpecialFunctionProofAgent.'
SIMPS = ('SpecialFunctionProofAgent.evalPolynomial, SpecialFunctionProofAgent.primitivePolynomial, '
         'SpecialFunctionProofAgent.finiteExponentialCombination, List.map_cons, List.map_nil, '
         'List.sum_cons, List.sum_nil, Prod.fst, Prod.snd')


def parameters(node):
    from .real_bessel import _walk
    bound = {node.get(key) for key in ('index', 'var', 'state')}
    return {item['name']: 'real' for item in _walk(node) if item.get('op') == 'var'
            and item.get('name') not in bound}


def normalized(node):
    return syntax.normalize(node, parameters(node))


def name(node):
    raw = json.dumps(node, sort_keys=True, ensure_ascii=False, separators=(',', ':')).encode()
    return 'ResearchAnalytic_' + _sha(raw)


def _int(value): return {'op': 'int', 'value': value}
def _bin(op, left, right): return {'op': op, 'args': [left, right]}


def _sum(values):
    if not values: return _int(0)
    if len(values) > 8:
        middle = len(values)//2
        return _bin('add', _sum(values[:middle]), _sum(values[middle:]))
    result = values[0]
    for value in values[1:]: result = _bin('add', result, value)
    return result


def primitive(coefficients, arg):
    power = lambda degree: ({'op': 'pow', 'base': deepcopy(arg), 'exponent': degree+1}
                            if degree < 12 else _bin('mul', {'op': 'pow', 'base': deepcopy(arg),
                                                            'exponent': degree}, deepcopy(arg)))
    return _sum([_bin('div', _bin('mul', deepcopy(c), power(degree)), _int(degree+1))
                 for degree, c in enumerate(coefficients) if c != _int(0)])


def expand(node):
    data = normalized(node)
    if node['op'] == 'series_definition':
        result = _sum([_bin('mul', deepcopy(term['coefficient']),
                           {'op': 'exp', 'arg': deepcopy(term['argument'])}) for term in data['terms']])
    elif node['op'] == 'integral_definition':
        result = _bin('sub', primitive(data['coefficients'], data['upper']),
                      primitive(data['coefficients'], data['lower']))
    else:
        delta = _bin('sub', primitive(data['coefficients'], data['arg']),
                     primitive(data['coefficients'], data['initial_time']))
        result = _bin('mul', deepcopy(data['initial_value']), {'op': 'exp', 'arg': delta})
    # Keep original scalar-domain obligations visible after coefficient cancellation.
    # Zero witnesses preserve the real expression and the existing domain checker.
    from .real_bessel import _walk
    sensitive = {'div', 'gamma', 'rpow', 'sqrt', 'bessel_j', 'bessel_y', 'bessel_y_noninteger', 'bessel_cross'}
    for scalar in data['scalar_expressions']:
        if any(item.get('op') in sensitive for item in _walk(scalar)):
            result = _bin('add', result, _bin('mul', _int(0), deepcopy(scalar)))
    for denominator in data['nonzero_denominators']:
        result = _bin('add', result, _bin('mul', _int(0), _bin('div', _int(1), deepcopy(denominator))))
    return result


def _terms(data, render):
    if data['op'] == 'series_definition':
        pairs = [f'({render(t["coefficient"])}, {render(t["argument"])})' for t in data['terms']]
        return '(['+', '.join(pairs)+'] : List (ℝ × ℝ))'
    pairs = [f'({render(c)}, {degree})' for degree, c in enumerate(data['coefficients']) if c != _int(0)]
    return '(['+', '.join(pairs)+'] : List (ℝ × ℕ))'


def _fresh(names, prefix):
    index = 0
    while prefix+str(index) in names.values(): index += 1
    return prefix+str(index)


def render(node, names, types, infos):
    from .research_functions import _lean
    data = normalized(node)
    child = lambda expr: _lean(expr, names, types, infos)
    if node['op'] == 'series_definition':
        k = _fresh(names, 'uk')
        body = _lean(node['term'], {**names, node['index']: k}, {**types, node['index']: 'nat'}, infos)
        return f'(∑\' ({k} : ℕ), {body})'
    if node['op'] == 'integral_definition':
        t = _fresh(names, 'ut')
        body = _lean(node['integrand'], {**names, node['var']: t}, {**types, node['var']: 'real'}, infos)
        return f'(∫ {t} in {child(node["lower"])}..{child(node["upper"])}, {body})'
    return (f'({NS}polynomialIVPSolution {_terms(data, child)} '
            f'({child(node["initial_time"])}) ({child(node["initial_value"])}) ({child(node["arg"])}))')


def declarations(node):
    """Prove the original user expression and the normalized analytic theorem agree."""
    from .research_functions import _lean
    data = normalized(node)
    types = parameters(node)
    names = {key: 'u'+str(i) for i, key in enumerate(sorted(types))}
    binders = ' '.join(f'({value} : ℝ)' for value in names.values())
    arguments = ' '.join(names.values())
    child = lambda expr: _lean(expr, names, types, {})
    terms = _terms(data, child)
    original = render(node, names, types, {})
    closed = child(expand(node))
    prefix = name(node)
    if node['op'] == 'series_definition':
        k = _fresh(names, 'uk')
        body = _lean(node['term'], {**names, node['index']: k}, {**types, node['index']: 'nat'}, {})
        proposition = f'HasSum (fun {k} : ℕ => {body}) ({closed})'
        proof = (f'  convert {NS}hasSum_factorialCombination {terms} using 1 <;>\n'
                 f'    first | (funext {k}; simp only [{SIMPS}] <;> ring) | (simp only [{SIMPS}] <;> ring)\n')
        bridge_proof = f'  exact ({prefix}_contract {arguments}).tsum_eq\n'
    elif node['op'] == 'integral_definition':
        t = _fresh(names, 'ut')
        body = _lean(node['integrand'], {**names, node['var']: t}, {**types, node['var']: 'real'}, {})
        lower, upper = child(node['lower']), child(node['upper'])
        proposition = f'IntervalIntegrable (fun {t} : ℝ => {body}) volume ({lower}) ({upper})'
        equality = (f'  have hfun : (fun {t} : ℝ => {body}) = {NS}evalPolynomial {terms} := by\n'
                    f'    funext {t}\n    simp only [{SIMPS}] <;> ring\n')
        proof = equality+f'  rw [hfun]\n  exact {NS}intervalIntegrable_evalPolynomial {terms} ({lower}) ({upper})\n'
        bridge_proof = (equality+f'  change (∫ {t} in ({lower})..({upper}), (fun {t} : ℝ => {body}) {t}) = _\n'
                        f'  rw [hfun]\n  change {NS}polynomialIntegral {terms} ({lower}) ({upper}) = _\n'
                        f'  rw [{NS}polynomialIntegral_eq_primitive_sub] <;> simp only [{SIMPS}] <;> ring\n')
    else:
        t, v = _fresh(names, 'ut'), _fresh(names, 'uy')
        rhs = _lean(node['rhs'], {**names, node['var']: t, node['state']: v},
                    {**types, node['var']: 'real', node['state']: 'real'}, {})
        rhs_y = _lean(node['rhs'], {**names, node['var']: t, node['state']: f'(y {t})'},
                      {**types, node['var']: 'real', node['state']: 'real'}, {})
        time, initial = child(node['initial_time']), child(node['initial_value'])
        proposition = f'∃! y : ℝ → ℝ, (∀ {t}, HasDerivAt y ({rhs_y}) {t}) ∧ y ({time}) = ({initial})'
        proof = (f'  have hrhs ({t} {v} : ℝ) : {rhs} = {NS}evalPolynomial {terms} {t} * {v} := by\n'
                 f'    simp only [{SIMPS}] <;> ring\n'
                 f'  simpa only [hrhs] using {NS}existsUnique_polynomialIVPSolution {terms} ({time}) ({initial})\n')
        bridge_proof = f'  rw [{NS}polynomialIVPSolution_eq_exp] <;> simp only [{SIMPS}] <;> ring\n'
    return (f'theorem {prefix}_contract {binders} : {proposition} := by\n'+proof+'\n'
            +f'theorem {prefix}_bridge {binders} : {original} = {closed} := by\n'+bridge_proof,
            proposition, names)


def contract(node):
    data = normalized(node)
    kind = {'series_definition': 'user_factorial_series', 'integral_definition': 'user_polynomial_integral',
            'ode_definition': 'user_polynomial_coefficient_ivp'}[node['op']]
    semantics = {'original': deepcopy(node), 'normalized': data, 'parameter_domain': 'real'}
    if node['op'] == 'series_definition':
        semantics.update(index_domain='nat', first_index=0, convergence='HasSum and Summable')
    elif node['op'] == 'integral_definition':
        semantics.update(orientation='lower_to_upper', endpoints='arbitrary finite reals')
    else:
        semantics.update(solution_class='real functions satisfying HasDerivAt at every real time',
                         initial_time=deepcopy(node['initial_time']), initial_value=deepcopy(node['initial_value']))
    return {'op': node['op'], 'kind': kind, 'domain': parameters(node), 'semantics': semantics,
            'definition': name(node), 'bridge': name(node)+'_bridge', 'theorems': [name(node)+'_contract']}
