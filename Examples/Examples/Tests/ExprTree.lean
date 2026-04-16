import TreeKernel

open TreeKernel

def leanEnv : TreeKernel.Env := _root_.Env.empty

-- === Sort ===
#eval infer leanEnv (.sort .zero)
#eval infer leanEnv (.sort Level.one)

-- === BVar ===
#eval infer leanEnv (.bvar 0) [.sort .zero]

-- === Lambda ===
#eval infer leanEnv (.lam (.sort .zero) (.bvar 0))

-- === App ===
#eval infer leanEnv (.app (.lam (.sort .zero) (.bvar 0)) (.sort .zero))

-- === ForallE (Pi) ===
#eval infer leanEnv (.forallE (.sort .zero) (.sort .zero))
