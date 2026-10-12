/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Fundamental

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicCycle

variable (X : Scheme.{u}) [IsLocallyNoetherian X]

#check (fundamental : (X → ℤ) → ℤ → AlgebraicCycle X ℤ)

end AlgebraicGeometry.AlgebraicCycle
