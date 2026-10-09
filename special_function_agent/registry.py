"""Small, versioned mathematical conventions shared by identity and evidence."""
BASE_FAMILIES = {
    'bessel_j': {'module': 'BesselProofAgent', 'definition': 'Complex.besselJ; v2 positive real J diagnostics', 'formal_scope': 'v1 fixed recipes'},
    'bessel_y': {'module': None, 'definition': 'standard real Bessel Y on positive arguments', 'formal_scope': 'pending'},
    'bessel_cross': {'module': None, 'definition': 'X_nm(s,t)=J_n(s)*Y_m(t)-Y_n(s)*J_m(t)', 'formal_scope': 'conditional algebra'},
    'gamma': {'module': 'SpecialFunctionProofAgent.Gamma', 'definition': 'Real.Gamma', 'formal_scope': 'positive recurrence and scaled integral'},
    'beta': {'module': 'SpecialFunctionProofAgent.Beta', 'definition': 'integral 0..1 of t^(a-1)*(1-t)^(b-1), a,b>0', 'formal_scope': 'real Euler beta integral'},
}
CONVENTIONS = {'version': 1, 'families': BASE_FAMILIES, 'scalars': 'Lean Real',
               'rpow': 'Real.rpow', 'exp': 'Real.exp',
               'finite_integral': 'oriented intervalIntegral, volume',
               'infinite_integral': 'MeasureTheory integral on Set.Ioi lower, volume'}


FAMILIES = {**BASE_FAMILIES,
    'hermite_h': {'module': 'SpecialFunctionProofAgent.Hermite', 'definition': 'physicists H_n, natural degree; H_n(x)=sqrt(2)^n*He_n(sqrt(2)*x)', 'formal_scope': 'derivative, recurrence and initial values'},
    'hermite_he': {'module': 'SpecialFunctionProofAgent.Hermite', 'definition': 'probabilists He_n, Polynomial.hermite evaluated over Real, natural degree', 'formal_scope': 'derivative and initial values'},
    'erf': {'module': 'SpecialFunctionProofAgent.Erf', 'definition': 'erf(x)=2/sqrt(pi)*integral 0..x exp(-t^2), x real', 'formal_scope': 'derivative, zero, oddness and Gaussian finite integral'},
}


def conventions(data):
    """Keep the original families' identity stable while versioning new conventions."""
    def contains_new(node):
        if isinstance(node, dict):
            return node.get('op') in {'hermite_h', 'hermite_he', 'erf'} or any(contains_new(v) for v in node.values())
        return isinstance(node, list) and any(contains_new(v) for v in node)
    if contains_new([data.get('lhs'), data.get('rhs'), data.get('assumptions', [])]):
        return {**CONVENTIONS, 'version': 2, 'families': FAMILIES,
                'hermite_degree': 'natural number; subtraction requires the stated lower bound',
                'derivative': 'real derivative in the explicitly named variable, at its current value'}
    return CONVENTIONS
