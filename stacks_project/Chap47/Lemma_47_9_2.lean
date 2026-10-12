/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.Restriction
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.LocalCohomology

/- Lemma 47.9.2: for a finitely generated ideal `I`, local cohomology with
   support commutes functorially with restriction of scalars along `f`. -/
@[stacks 0BJB]
#check (CategoryTheory.DerivedCategory.LocalCohomology.restrictionComparisonIsIso :
  ∀ {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (I : Ideal A) (hI : I.FG)
    (RΓA : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I)
    (RΓB : DerivedCategory (ModuleCat B) ⥤ IdealPowerTorsion (I.map f))
    (hA : IdealPowerTorsion.inclusion I ⊣ RΓA)
    (hB : IdealPowerTorsion.inclusion (I.map f) ⊣ RΓB),
    IsIso (restrictionComparison f I hI RΓA RΓB hA hB))

end CategoryTheory.DerivedCategory.LocalCohomology
