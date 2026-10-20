module

public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Fundamental

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicCycle

variable (X : Scheme.{u}) [IsLocallyNoetherian X]

#check (fundamental : (X → ℤ) → ℤ → AlgebraicCycle X ℤ)

end AlgebraicGeometry.AlgebraicCycle
