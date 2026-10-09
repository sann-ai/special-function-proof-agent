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


CLASSICAL_FAMILY_NAMES = tuple(FAMILIES)
FAMILIES.update({
    'bessel_y_noninteger': {'module': 'SpecialFunctionProofAgent.BesselY', 'definition': 'DLMF 10.2.3 real positive-axis Y from Complex.besselJ; fixed orders -1/2,1/2,3/2', 'formal_scope': 'half-order recurrence and symmetric derivative; x>0'},
    'legendre': {'module': 'SpecialFunctionProofAgent.Legendre', 'definition': 'standard P_n(x)=shiftedLegendre_n((1-x)/2), natural degree', 'formal_scope': 'parity, endpoints and degrees zero through two'},
    'laguerre': {'module': 'SpecialFunctionProofAgent.Laguerre', 'definition': 'DLMF 18.5.12 generalized L_n^(alpha), finite polynomial sum for real alpha; L_n means alpha=0', 'formal_scope': 'derivative lowering degree and raising alpha; initial values'},
    'jacobi': {'module': 'SpecialFunctionProofAgent.Jacobi', 'definition': 'DLMF 18.5.7 P_n^(alpha,beta), finite polynomial sum for real alpha,beta', 'formal_scope': 'derivative lowering degree and raising both parameters; initial values; Legendre specialization'},
})


def conventions(data):
    """Keep the original families' identity stable while versioning new conventions."""
    def contains(node, ops):
        if isinstance(node, dict):
            return node.get('op') in ops or any(contains(v, ops) for v in node.values())
        return isinstance(node, list) and any(contains(v, ops) for v in node)
    nodes = [data.get('lhs'), data.get('rhs'), data.get('assumptions', [])]
    if contains(nodes, {'legendre', 'laguerre', 'jacobi', 'bessel_y_noninteger'}):
        return {**CONVENTIONS, 'version': 3, 'families': FAMILIES,
                'polynomial_degree': 'natural number; subtraction requires the stated lower bound',
                'polynomial_parameters': 'real finite polynomial extension; Laguerre alpha=0 is the ordinary convention',
                'derivative': 'real derivative in the explicitly named variable, at its current value'}
    if contains(nodes, {'hermite_h', 'hermite_he', 'erf'}):
        return {**CONVENTIONS, 'version': 2, 'families': {k: FAMILIES[k] for k in CLASSICAL_FAMILY_NAMES},
                'hermite_degree': 'natural number; subtraction requires the stated lower bound',
                'derivative': 'real derivative in the explicitly named variable, at its current value'}
    return CONVENTIONS
