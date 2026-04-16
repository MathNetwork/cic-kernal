import HypergraphKernel

def astroNet := AstroNet.empty

-- === Sort ===
#eval infer astroNet (.sort .zero)
#eval infer astroNet (.sort Level.one)

-- === BVar ===
#eval infer astroNet (.bvar 0) [.sort .zero]

-- === Lambda ===
#eval infer astroNet (.lam (.sort .zero) (.bvar 0))

-- === App ===
#eval infer astroNet (.app (.lam (.sort .zero) (.bvar 0)) (.sort .zero))

-- === ForallE (Pi) ===
#eval infer astroNet (.forallE (.sort .zero) (.sort .zero))
