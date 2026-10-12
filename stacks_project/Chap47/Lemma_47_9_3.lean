/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.BaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 47.9.3: for a finitely generated ideal `I`, local cohomology commutes
functorially with derived extension of scalars along any ring homomorphism `f`, with
the support over `B` defined by `I.map f`. -/
@[stacks 0ALZ] #check
  (CategoryTheory.DerivedCategory.LocalCohomology.comparisonIsIso :
    ∀ {A B : Type u} [CommRing A] [CommRing B]
      (f : A →+* B) (I : Ideal A) (hI : I.FG)
      (RΓA : DerivedCategory (ModuleCat A) ⥤
        CategoryTheory.DerivedCategory.IdealPowerTorsion I)
      (RΓB : DerivedCategory (ModuleCat B) ⥤
        CategoryTheory.DerivedCategory.IdealPowerTorsion (I.map f))
      (hA : CategoryTheory.DerivedCategory.IdealPowerTorsion.inclusion I ⊣ RΓA)
      (hB : CategoryTheory.DerivedCategory.IdealPowerTorsion.inclusion (I.map f) ⊣ RΓB),
      IsIso
        (CategoryTheory.DerivedCategory.LocalCohomology.BaseChange.comparison
          f I hI RΓA RΓB hA hB))
