"""Small, versioned mathematical conventions shared by identity and evidence."""
FAMILIES = {
    'bessel_j': {'module': 'BesselProofAgent', 'definition': 'Complex.besselJ; v2 positive real J diagnostics', 'formal_scope': 'v1 fixed recipes'},
    'bessel_y': {'module': None, 'definition': 'standard real Bessel Y on positive arguments', 'formal_scope': 'pending'},
    'bessel_cross': {'module': None, 'definition': 'X_nm(s,t)=J_n(s)*Y_m(t)-Y_n(s)*J_m(t)', 'formal_scope': 'conditional algebra'},
    'gamma': {'module': 'SpecialFunctionProofAgent.Gamma', 'definition': 'Real.Gamma', 'formal_scope': 'positive recurrence and scaled integral'},
    'beta': {'module': 'SpecialFunctionProofAgent.Beta', 'definition': 'integral 0..1 of t^(a-1)*(1-t)^(b-1), a,b>0', 'formal_scope': 'real Euler beta integral'},
}
CONVENTIONS = {'version': 1, 'families': FAMILIES, 'scalars': 'Lean Real',
               'rpow': 'Real.rpow', 'exp': 'Real.exp',
               'finite_integral': 'oriented intervalIntegral, volume',
               'infinite_integral': 'MeasureTheory integral on Set.Ioi lower, volume'}
