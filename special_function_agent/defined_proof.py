"""Connect finite research definitions to the existing fixed proof renderers."""
from .core import InputError
from . import real_special, research_functions as functions

FORMAL_SCOPE = 'proof of the original real target under explicit finite research definitions'


def formal_scope(data):
    return ('proof of the original real target under verified analytic research definitions'
            if functions.uses_analytic(data.get('definitions', [])) else FORMAL_SCOPE)


def conventions(data):
    from .registry import conventions as ordinary_conventions
    if not functions.contains(data):
        from . import research_advanced_analytic_lean as advanced
        return {**ordinary_conventions(data), **({'advanced_real_functions': dict(advanced.SCALAR_CONVENTIONS)}
                if functions.uses_advanced_analytic(data) else {})}
    from . import research_advanced_analytic_lean as advanced
    return {**ordinary_conventions(functions.expand_target(data)),
            **({'advanced_real_functions': dict(advanced.SCALAR_CONVENTIONS)} if functions.uses_advanced_analytic(data) else {}),
            'research_definitions': functions.metadata(data['definitions']),
            'research_definition_semantics': ('explicit real expressions and verified closed analytic forms; simultaneous typed parameter substitution'
                if functions.uses_analytic(data['definitions']) else
                'finite explicit real expressions; simultaneous typed parameter substitution')}


def display(data, node):
    from .real_bessel import display as ordinary_display, _walk
    from . import research_analytic as analytic
    from . import research_user_analytic_lean as user_analytic
    from . import research_advanced_analytic_lean as advanced
    if isinstance(node, dict) and node.get('op') in advanced.OPS:
        child = lambda value: display(data, value)
        if node['op'] == 'geometric_series_definition':
            return 'sum('+node['index']+'=0..infinity, '+child(node['term'])+')'
        if node['op'] == 'elementary_integral_definition':
            return 'integral('+child(node['lower'])+'..'+child(node['upper'])+', '+child(node['integrand'])+' d'+node['var']+')'
        time, initial = child(node['initial_time']), child(node['initial_value'])
        degree = "''" if node['op'] == 'second_order_ode_definition' else "'"
        velocity = (', '+node['state']+"'("+time+')='+child(node['initial_derivative'])) if degree == "''" else ''
        return 'IVP('+node['state']+degree+'='+child(node['rhs'])+', '+node['state']+'('+time+')='+initial+velocity+'; '+node['var']+'='+child(node['arg'])+')'
    if isinstance(node, dict) and node.get('op') in user_analytic.OPS:
        child = lambda value: display(data, value)
        if node['op'] == 'series_definition':
            return 'sum('+node['index']+'=0..infinity, '+child(node['term'])+')'
        if node['op'] == 'integral_definition':
            return 'integral('+child(node['lower'])+'..'+child(node['upper'])+', '+child(node['integrand'])+' d'+node['var']+')'
        return ("IVP("+node['state']+"'="+child(node['rhs'])+', '+node['state']+'('
                +child(node['initial_time'])+')='+child(node['initial_value'])+'; '
                +node['var']+'='+child(node['arg'])+')')
    if isinstance(node, dict) and node.get('op') == 'factorial': return display(data, node['arg'])+'!'
    if isinstance(node, dict) and node.get('op') == 'pow' and isinstance(node['exponent'], dict):
        return '('+display(data, node['base'])+')^('+display(data, node['exponent'])+')'
    if isinstance(node, dict) and any(item.get('op') in {'factorial'} or
          item.get('op') == 'pow' and isinstance(item.get('exponent'), dict)
          for item in _walk(node)):
        if node['op'] == 'neg': return '-('+display(data, node['arg'])+')'
        if node['op'] in {'add', 'sub', 'mul', 'div'}:
            symbol = {'add': '+', 'sub': '-', 'mul': '*', 'div': '/'}[node['op']]
            return '('+display(data, node['args'][0])+symbol+display(data, node['args'][1])+')'
    if isinstance(node, dict) and node.get('op') in analytic.OPS:
        analytic.fields(node)
        args = {name: display(data, node[name]) for name in analytic.fields(node)}
        if node['op'] == 'exp_series': return 'sum(n=0..infinity, ('+args['arg']+')^n/n!)'
        if node['op'] == 'gaussian_primitive': return 'integral(0..'+args['arg']+', exp(-t^2) dt)'
        return "IVP(y'= ("+args['rate']+")*y, y(0)="+args['initial']+'; t='+args['arg']+')'
    result = ordinary_display(node)
    for item in functions.metadata(data['definitions']):
        result = result.replace('Function['+item['id']+']', item['name'])
    return result


def definition_lines(data):
    snapshots = {}
    def collect(items):
        for item in items:
            collect(item['definitions'])
            snapshots[item['id']] = item
    collect(data['definitions'])
    lines = []
    for item in snapshots.values():
        lines.append('- '+item['name']+'('+', '.join(name+': real' for name in sorted(item['parameters']))+') = '
                     +display(data, item['body'])+'。定義ID：'+item['id'])
    for item in functions.metadata(data['definitions']):
        for contract in item.get('analytic_contracts', []):
            statement = {
                'exp_series': '全実引数で階乗級数の HasSum と収束を検証し、exp との等式を適用します。',
                'gaussian_primitive': '0から実端点への有向区間で可積分性を検証し、sqrt(pi)/2 * erf との等式を適用します。',
                'linear_ivp': "rate と initial を固定し、全実数上の各点で y'=rate*y を満たし y(0)=initial となる関数の存在・一意性を検証します。",
                'geometric_series_definition': '入力一般項を幾何核の有限線形結合へ接続し、各底の絶対値が1未満であることと HasSum・収束を Lean で検証します。',
                'elementary_integral_definition': '固定有理傾きのexp/sin/cos有限線形結合と元被積分式の一致、指定実端点間の可積分性・原始関数公式を Lean で検証します。傾き0と逆向き区間を含みます。',
                'nonlinear_ode_definition': '元右辺 p(t)*sqrt(1+y^2) と初期条件を固定し、全実時間の各点で微分条件を満たす実関数の存在一意性を、arsinh変換から Lean で検証します。',
                'second_order_ode_definition': '元二階式 y\'\'=p(t) を位置・速度の組の y\'=v, v\'=p(t) へ接続します。全実時間の両微分条件と独立な位置・速度初期値を満たす組の存在一意性を Lean で検証します。',
                'series_definition': '入力された一般項と階乗核の有限線形結合の一致、および HasSum・収束を Lean で検証します。係数と核引数は自然数の和変数に依存しません。',
                'integral_definition': '入力された被積分多項式との一致と、指定した実端点間の有向積分の可積分性・原始関数公式を Lean で検証します。',
                'ode_definition': '入力された右辺・初期時刻・初期値を保持し、全実数上の各点でその微分条件を満たす実関数の存在一意性を Lean で検証します。',
            }[contract['op']]
            lines.append('- '+item['name']+' の定義根拠：'+statement+' 橋渡し：'+contract['bridge'])
    return lines


def wrap_body(data, body):
    """Keep the original function calls in a theorem proved by definitional unfolding."""
    marker = 'theorem target '
    if body.count(marker) != 1:
        raise InputError('A defined-function proof needs one generated target theorem.')
    body = body.replace(marker, 'theorem expanded_target ', 1)
    names = {name: f'v{i}' for i, name in enumerate(sorted(data['variables']))}
    types = data['variables']
    definitions = data['definitions']
    expr = lambda node: functions.lean_expr(node, names, types, definitions)
    binders = ' '.join(f'({names[name]} : ℝ)' for name in sorted(names))
    conditions = []
    from .real_bessel import RELATIONS
    for i, atom in enumerate(data['assumptions']):
        if atom['op'] == 'expr_compare':
            relation = RELATIONS[atom['relation']].replace('!=', '≠').replace('>=', '≥').replace('<=', '≤')
            text = f'{expr(atom["lhs"])} {relation} (0 : ℝ)'
        else:
            text = real_special._condition(atom, names, types)
        conditions.append(f'(h{i} : {text})')
    arguments = ' '.join([*names.values(), *(f'h{i}' for i in range(len(conditions)))])
    # `exact` checks definitional equality through the regenerated definitions,
    # including their occurrence in the original assumptions.
    if functions.uses_analytic(definitions):
        rewrite = ', '.join(functions.rewrite_lemmas(definitions))
        arguments = ' '.join([*names.values(), *(f'(by simpa only [{rewrite}] using h{i})' for i in range(len(conditions)))])
        proof = f'  simpa only [{rewrite}] using (expanded_target {arguments})\n'
    else:
        proof = f'  exact expanded_target {arguments}\n'
    wrapper = (f'theorem target {binders} {" ".join(conditions)} : '
               f'{expr(data["lhs"])} = {expr(data["rhs"])} := by\n'
               +proof)
    return functions.lean_definitions(definitions)+'\n\n'+body+'\n'+wrapper


def render(data):
    from . import research_proof
    functions.validate_target(data)
    if research_proof.is_research(data):
        return research_proof.render(data)
    expanded = functions.expand_target(data)
    source = real_special.render(expanded, definition_context=True)
    body = research_proof._ordinary_body(source)
    return research_proof._source(wrap_body(data, body), [])


def analysis(data, ordinary_analysis):
    expanded = functions.expand_target(data)
    return {'recipe': 'defined_functions', 'definitions': functions.metadata(data['definitions']),
            'expanded_target': {key: value for key, value in expanded.items() if key != 'proof'},
            'proof_analysis': ordinary_analysis}


def default_proof(data, route='direct'):
    from copy import deepcopy
    proof = real_special.default_proof(functions.expand_target(data), route)
    if route == 'steps':
        from .real_bessel import labels
        proof['steps'][0].update(before=deepcopy(data['lhs']), after=deepcopy(data['rhs']),
                                 conditions=labels(data))
        proof['steps'][0]['reason'] = '保存した明示定義を展開する。'+proof['steps'][0]['reason']
    return proof
