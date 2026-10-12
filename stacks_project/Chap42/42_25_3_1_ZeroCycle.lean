/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.ZeroCycle.Components

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable (Y : Scheme.{u}) [IsLocallyNoetherian Y]

#check (zeroCycle :
  ∀ (d : Y → ℤ) (ℒ : Y.Modules) [Invertible ℒ],
    ℒ.sections → ℤ → AlgebraicCycle Y ℤ)

end AlgebraicGeometry.Scheme.Modules
