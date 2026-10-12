/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.ProjectiveSpace.Beilinson.Generator

open CategoryTheory.Limits

universe u

/- 36.20.0.1: on standard projective `n`-space over `R`, the object `P` is
`∐ fun i : Fin (n + 1) ↦ twistingSheaf R n (-(i : ℤ))`. -/
@[stacks 0CS8] #check
  (AlgebraicGeometry.ProjectiveSpace.beilinsonGenerator_def :
    ∀ (R : Type u) [CommRing R] (n : ℕ),
      AlgebraicGeometry.ProjectiveSpace.beilinsonGenerator R n =
        ∐ fun i : Fin (n + 1) ↦
          AlgebraicGeometry.ProjectiveSpace.twistingSheaf R n (-(i : ℤ)))
