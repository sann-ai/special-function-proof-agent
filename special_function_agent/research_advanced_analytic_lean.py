"""Verifier-owned bridges for bounded geometric, elementary and ODE definitions."""
from copy import deepcopy
import json

from .core import _sha
from . import research_advanced_analytic as syntax
from .research_user_analytic_lean import _int, _bin, _sum, primitive, _fresh

OPS = {'geometric_series_definition', 'elementary_integral_definition',
       'nonlinear_ode_definition', 'second_order_ode_definition'}
SCALAR_OPS = {'sin', 'cos', 'sinh', 'arsinh'}
SCALAR_CONVENTIONS = {op: 'Real.'+op+' on all real arguments' for op in sorted(SCALAR_OPS)}
NS = 'SpecialFunctionProofAgent.'
SIMPS = ('SpecialFunctionProofAgent.evalPolynomial, SpecialFunctionProofAgent.primitivePolynomial, '
         'List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Prod.fst, Prod.snd')


def parameters(node):
    from .real_bessel import _walk
    bound = {node.get(key) for key in ('index', 'var', 'state', 'velocity')}
    return {item['name']: 'real' for item in _walk(node) if item.get('op') == 'var'
            and item.get('name') not in bound}


def normalized(node): return syntax.normalize(node, parameters(node))


def name(node):
    raw = json.dumps(node, sort_keys=True, ensure_ascii=False, separators=(',', ':')).encode()
    return 'ResearchAdvanced_' + _sha(raw)


def _power(arg, exponent):
    if exponent <= 12: return {'op': 'pow', 'base': deepcopy(arg), 'exponent': exponent}
    return _bin('mul', _power(arg, 12), _power(arg, exponent-12))


def second_primitive(coefficients, arg):
    return _sum([_bin('div', _bin('div', _bin('mul', deepcopy(c), _power(arg, n+2)), _int(n+1)), _int(n+2))
                 for n, c in enumerate(coefficients) if c != _int(0)])


def _affine(term, arg):
    return _bin('add', _bin('mul', deepcopy(term['slope']), deepcopy(arg)), deepcopy(term['intercept']))


def _elementary_primitive(terms, arg):
    from .core import _constant
    values = []
    for term in terms:
        a = _constant(term['slope'])
        if a == 0:
            base = _bin('mul', deepcopy(arg), {'op': term['kind'], 'arg': deepcopy(term['intercept'])})
        else:
            kind = {'exp': 'exp', 'sin': 'cos', 'cos': 'sin'}[term['kind']]
            base = {'op': kind, 'arg': _affine(term, arg)}
            if term['kind'] == 'sin': base = {'op': 'neg', 'arg': base}
            base = _bin('div', base, deepcopy(term['slope']))
        values.append(_bin('mul', deepcopy(term['coefficient']), base))
    return _sum(values)


def expand(node):
    data = normalized(node)
    if node['op'] == 'geometric_series_definition':
        result = _sum([_bin('div', deepcopy(term['coefficient']), _bin('sub', _int(1), deepcopy(term['argument'])))
                       for term in data['terms']])
    elif node['op'] == 'elementary_integral_definition':
        result = _bin('sub', _elementary_primitive(data['terms'], data['upper']),
                      _elementary_primitive(data['terms'], data['lower']))
    elif node['op'] == 'nonlinear_ode_definition':
        delta = _bin('sub', primitive(data['coefficients'], data['arg']),
                     primitive(data['coefficients'], data['initial_time']))
        result = {'op': 'sinh', 'arg': _bin('add', {'op': 'arsinh', 'arg': deepcopy(data['initial_value'])}, delta)}
    else:
        t0, x = data['initial_time'], data['arg']
        delta = _bin('sub', deepcopy(x), deepcopy(t0))
        correction = _bin('sub', _bin('sub', second_primitive(data['coefficients'], x),
                                    second_primitive(data['coefficients'], t0)),
                          _bin('mul', primitive(data['coefficients'], t0), deepcopy(delta)))
        result = _bin('add', _bin('add', deepcopy(data['initial_value']),
                                  _bin('mul', deepcopy(data['initial_derivative']), delta)), correction)
    from .real_bessel import _walk
    sensitive = {'div', 'gamma', 'rpow', 'sqrt', 'bessel_j', 'bessel_y', 'bessel_y_noninteger', 'bessel_cross'}
    for scalar in data['scalar_expressions']:
        if any(item.get('op') in sensitive for item in _walk(scalar)):
            result = _bin('add', result, _bin('mul', _int(0), deepcopy(scalar)))
    for denominator in data['nonzero_denominators']:
        result = _bin('add', result, _bin('mul', _int(0), _bin('div', _int(1), deepcopy(denominator))))
    return result


def _terms(data, render):
    if data['op'] == 'geometric_series_definition':
        return '(['+', '.join(f'({render(t["coefficient"])}, {render(t["argument"])})' for t in data['terms'])+'] : List (ℝ × ℝ))'
    if data['op'] == 'elementary_integral_definition':
        return ' '.join('(['+', '.join(f'({render(t["coefficient"])}, {render(t["slope"])}, {render(t["intercept"])})'
                        for t in data['terms'] if t['kind'] == kind)+'] : List (ℝ × ℝ × ℝ))'
                        for kind in ('exp', 'sin', 'cos'))
    return '(['+', '.join(f'({render(c)}, {degree})' for degree, c in enumerate(data['coefficients']) if c != _int(0))+'] : List (ℝ × ℕ))'


def render(node, names, types, infos):
    from .research_functions import _lean
    data = normalized(node)
    child = lambda expr: _lean(expr, names, types, infos)
    if node['op'] == 'geometric_series_definition':
        k = _fresh(names, 'ak')
        body = _lean(node['term'], {**names, node['index']: k}, {**types, node['index']: 'nat'}, infos)
        return f'(∑\' ({k} : ℕ), {body})'
    if node['op'] == 'elementary_integral_definition':
        t = _fresh(names, 'at')
        body = _lean(node['integrand'], {**names, node['var']: t}, {**types, node['var']: 'real'}, infos)
        return f'(∫ {t} in {child(node["lower"])}..{child(node["upper"])}, {body})'
    fn = 'nonlinearPolynomialIVPSolution' if node['op'] == 'nonlinear_ode_definition' else 'polynomialSecondOrderPosition'
    args = [child(node['initial_time']), child(node['initial_value'])]
    if node['op'] == 'second_order_ode_definition': args.append(child(node['initial_derivative']))
    args.append(child(node['arg']))
    return f'({NS}{fn} {_terms(data, child)} '+ ' '.join('('+arg+')' for arg in args)+')'


def geometric_denominator_positive(base):
    """Recognize only bases whose strict bound is certified during registration."""
    from .core import InputError
    from .real_bessel import _walk
    params = {n['name']: 'real' for n in _walk(base) if n.get('op') == 'var'}
    binder = 'advancedIndex'
    while binder.casefold() in {n.casefold() for n in params}: binder += 'x'
    try:
        syntax.normalize({'op':'geometric_series_definition','index':binder,
                          'term':{'op':'pow','base':base,'exponent':{'op':'var','name':binder}}}, params)
        return True
    except InputError:
        return False


def declarations(node):
    from .research_functions import _lean
    from .real_bessel import _walk
    data = normalized(node)
    types = parameters(node)
    names = {key:'u'+str(i) for i,key in enumerate(sorted(types))}
    binders = ' '.join(f'({value} : ℝ)' for value in names.values())
    arguments = ' '.join(names.values())
    child = lambda expr: _lean(expr,names,types,{})
    terms = _terms(data, child)
    original, closed, prefix = render(node,names,types,{}), child(expand(node)), name(node)
    if node['op'] == 'geometric_series_definition':
        k = _fresh(names, 'ak')
        body = _lean(node['term'],{**names,node['index']:k},{**types,node['index']:'nat'},{})
        proposition = f'HasSum (fun {k} : ℕ => {body}) ({closed})'
        bound_proof = f'  have hbound : ∀ term ∈ {terms}, |term.2| < 1 := by\n    intro term ht\n'
        if not data['terms']:
            bound_proof += '    simp only [List.not_mem_nil] at ht\n'
        else:
            bound_proof += '    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht\n'
            bound_proof += '    rcases ht with '+' | '.join('rfl' for _ in data['terms'])+'\n'
            for term in data['terms']:
                if term['base_kind'] == 'rational': bound_proof += '    · norm_num\n'
                else:
                    base = child(term['base_argument'])
                    sign = term['base_sign']
                    standard = f'({base}) / (1 + ({base}) ^ 2)'
                    signed = standard if sign == 1 else f'-({standard})'
                    bound_proof += (f'    · have hbase : {child(term["argument"])} = {signed} := by\n'
                                    f'        ring_nf\n'
                                    f'      change |{child(term["argument"])}| < 1\n'
                                    f'      rw [hbase]\n'
                                    f'      simpa only [abs_neg] using {NS}abs_div_one_add_sq_lt_one ({base})\n')
        proof = (bound_proof+f'  convert {NS}hasSum_geometricCombination {terms} hbound using 1 <;>\n'
                 f'    first | (funext {k}; simp only [{SIMPS}, {NS}finiteGeometricCombination] <;> ring) | (simp only [{SIMPS}, {NS}finiteGeometricCombination] <;> ring)\n')
        bridge_proof = f'  exact ({prefix}_contract {arguments}).tsum_eq\n'
    elif node['op'] == 'elementary_integral_definition':
        t = _fresh(names, 'at')
        local_names, local_types = {**names,node['var']:t},{**types,node['var']:'real'}
        render_t = lambda expr:_lean(expr,local_names,local_types,{})
        body = render_t(node['integrand'])
        lower,upper = child(node['lower']),child(node['upper'])
        proposition = f'IntervalIntegrable (fun {t} : ℝ => {body}) volume ({lower}) ({upper})'
        affine, unary_rules = '', []
        for i,item in enumerate(data['affine_arguments']):
            left = render_t(item['original'])
            right = f'({child(item["slope"])})*{t}+({child(item["intercept"])})'
            affine += f'  have ha{i} ({t} : ℝ) : {left} = {right} := by ring\n'
            kinds = sorted({n['op'] for n in _walk(node['integrand'])
                            if n.get('op') in {'exp','sin','cos'} and n.get('arg') == item['original']})
            for kind in kinds:
                lemma = f'hu{i}_{kind}'
                affine += (f'  have {lemma} ({t} : ℝ) : Real.{kind} ({left}) = Real.{kind} ({right}) := '
                           f'congrArg Real.{kind} (ha{i} {t})\n')
                unary_rules.append(f'{lemma} {t}')
        rules = ', '.join(unary_rules)
        rewrite = (f'    try simp only [{rules}]\n' if rules else '')
        equality = (affine+f'  have hfun : (fun {t} : ℝ => {body}) = {NS}elementaryCombination {terms} := by\n'
                    f'    funext {t}\n'+rewrite+f'    simp only [{SIMPS}, {NS}elementaryCombination] <;> ring\n')
        proof = equality+f'  rw [hfun]\n  exact {NS}intervalIntegrable_elementaryCombination {terms} ({lower}) ({upper})\n'
        bridge_proof = (equality+f'  change (∫ {t} in ({lower})..({upper}), (fun {t} : ℝ => {body}) {t}) = _\n'
                        f'  rw [hfun]\n  change {NS}elementaryIntegral {terms} ({lower}) ({upper}) = _\n'
                        f'  rw [{NS}elementaryIntegral_eq_primitive_sub]\n'
                        f'  norm_num [{SIMPS}, {NS}elementaryPrimitive, {NS}affineExpPrimitive, {NS}affineSinPrimitive, {NS}affineCosPrimitive] <;> ring\n')
    else:
        t,v = _fresh(names,'at'),_fresh(names,'ay')
        time,initial = child(node['initial_time']),child(node['initial_value'])
        local_names = {**names,node['var']:t,node['state']:v}
        local_types = {**types,node['var']:'real',node['state']:'real'}
        rhs = _lean(node['rhs'],local_names,local_types,{})
        if node['op'] == 'nonlinear_ode_definition':
            rhs_y = _lean(node['rhs'],{**local_names,node['state']:f'(y {t})'},local_types,{})
            proposition = f'∃! y : ℝ → ℝ, (∀ {t}, HasDerivAt y ({rhs_y}) {t}) ∧ y ({time}) = ({initial})'
            roots = [item for item in _walk(node['rhs']) if item.get('op') == 'sqrt' and
                     any(n.get('op')=='var' and n.get('name')==node['state'] for n in _walk(item))]
            root_proofs=''
            for i,item in enumerate(roots):
                root_proofs += f'  have hr{i} ({v} : ℝ) : {_lean(item["arg"],local_names,local_types,{})} = 1+{v}^2 := by ring\n'
            rules = ', '.join('hr'+str(i) for i in range(len(roots)))
            rewrite = (f'    try simp only [{rules}]\n' if rules else '')
            proof = (root_proofs+f'  have hrhs ({t} {v} : ℝ) : {rhs} = {NS}evalPolynomial {terms} {t} * Real.sqrt (1+{v}^2) := by\n'
                     +rewrite+f'    simp only [{SIMPS}] <;> ring\n'
                     +f'  simpa only [hrhs] using {NS}existsUnique_nonlinearPolynomialIVPSolution {terms} ({time}) ({initial})\n')
            bridge_proof = (f'  rw [{NS}nonlinearPolynomialIVPSolution_eq_sinh]\n'
                            f'  simp only [{SIMPS}]\n  congr 1 <;> ring\n')
        else:
            velocity = child(node['initial_derivative'])
            proposition = (f'∃! state : (ℝ → ℝ) × (ℝ → ℝ), '
                           f'(∀ {t}, HasDerivAt state.1 (state.2 {t}) {t}) ∧ '
                           f'(∀ {t}, HasDerivAt state.2 ({rhs}) {t}) ∧ '
                           f'state.1 ({time}) = ({initial}) ∧ state.2 ({time}) = ({velocity})')
            proof = (f'  have hrhs ({t} : ℝ) : {rhs} = {NS}evalPolynomial {terms} {t} := by\n'
                     f'    simp only [{SIMPS}] <;> ring\n'
                     f'  simpa only [hrhs] using {NS}existsUnique_polynomialSecondOrderSolution {terms} ({time}) ({initial}) ({velocity})\n')
            bridge_proof = (f'  simp only [{NS}polynomialSecondOrderPosition, {NS}secondPrimitivePolynomial, {SIMPS}] <;> ring\n')
    return (f'theorem {prefix}_contract {binders} : {proposition} := by\n'+proof+'\n'
            +f'theorem {prefix}_bridge {binders} : {original} = {closed} := by\n'+bridge_proof,
            proposition,names)


def contract(node):
    data = normalized(node)
    kind = {'geometric_series_definition':'bounded_geometric_series',
            'elementary_integral_definition':'elementary_affine_integral',
            'nonlinear_ode_definition':'nonlinear_sqrt_polynomial_ivp',
            'second_order_ode_definition':'second_order_polynomial_forcing_ivp'}[node['op']]
    semantics = {'original': deepcopy(node), 'normalized': data, 'parameter_domain':'real',
                 'elementary_functions': deepcopy(SCALAR_CONVENTIONS)}
    if node['op'] == 'geometric_series_definition':
        semantics.update(index_domain='nat',first_index=0,convergence='HasSum and Summable; each base has proved absolute value below one')
    elif node['op'] == 'elementary_integral_definition':
        semantics.update(orientation='lower_to_upper',endpoints='arbitrary finite reals')
    else:
        semantics.update(solution_class=('pairs of real position and velocity functions, with HasDerivAt position velocity and HasDerivAt velocity forcing at every real time'
                          if node['op'] == 'second_order_ode_definition' else
                          'real functions satisfying the original HasDerivAt equation at every real time'),
                         initial_time=deepcopy(node['initial_time']),initial_value=deepcopy(node['initial_value']))
        if node['op'] == 'second_order_ode_definition':
            semantics.update(initial_derivative=deepcopy(node['initial_derivative']),
                             second_derivative='velocity = deriv position; deriv velocity = forcing')
    return {'op':node['op'],'kind':kind,'domain':parameters(node),'semantics':semantics,
            'definition':name(node),'bridge':name(node)+'_bridge','theorems':[name(node)+'_contract']}
