/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.LocalCohomology.Artinian
public import ReasLib.CategoryTheory.InverseSystem.MittagLeffler.Artinian
public import ReasLib.CategoryTheory.InverseSystem.Sequential.FGModuleCat
public import Mathlib.Algebra.Category.FGModuleCat.Basic

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace localCohomology

/-- Local cohomology of a sequential inverse system of finite modules over a Noetherian local
ring satisfies the Mittag-Leffler condition in every degree. -/
theorem isMittagLeffler_of_finite
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (M : SequentialInverseSystem (FGModuleCat.{u} A)) (i : ℕ) :
    SequentialInverseSystem.IsMittagLeffler
      (M ⋙ (ModuleCat.isFG A).ι ⋙
        localCohomology (IsLocalRing.maximalIdeal A) i) := sorry

end localCohomology
