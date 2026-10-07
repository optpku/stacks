module

public import ReasLib.AlgebraicGeometry.NodalModel.Power

@[expose] public section

universe u

namespace AlgebraicGeometry.NodalModel

/-- The nodal power-model ring `R[x, y]/(x * y - π ^ n)`, with its legacy ring name. -/
abbrev Ring (R : Type u) [CommRing R] (π : R) (n : ℕ) :=
  Power.Ring R π n

#check (AlgebraicGeometry.NodalModel.Power.Ring :
  ∀ (R : Type u) [CommRing R], R → ℕ → Type u)

end AlgebraicGeometry.NodalModel
