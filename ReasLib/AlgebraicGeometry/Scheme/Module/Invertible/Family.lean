module

public import Mathlib.Data.Fin.VecNotation
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A two-term family of invertible scheme modules is pointwise invertible. -/
instance instInvertible_pair {X : Scheme.{u}} (H D : X.Modules)
    [Invertible H] [Invertible D] : ∀ index : Fin 2, Invertible (![H, D] index) := sorry

end AlgebraicGeometry.Scheme.Modules
