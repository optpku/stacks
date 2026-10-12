/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.DerivedCompletion
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 47.12.1 (1): the canonical map from `RΓ_Z(K)` to `RΓ_Z(K^∧)` is an
isomorphism in `D(A)`. -/
@[stacks 0A6W]
#check (@CategoryTheory.DerivedCategory.LocalCohomology.Completion.mapToDerivedCompletionIsIso :
  ∀ {A : Type u} [CommRing A] (I : Ideal A) (hI : I.FG)
    (RΓZ : DerivedCategory (ModuleCat A) ⥤
      CategoryTheory.DerivedCategory.IdealPowerTorsion I)
    (hRΓZ : CategoryTheory.DerivedCategory.IdealPowerTorsion.inclusion I ⊣ RΓZ)
    (K : DerivedCategory (ModuleCat A)),
    IsIso (CategoryTheory.DerivedCategory.LocalCohomology.Completion.mapToDerivedCompletion
      I hI RΓZ hRΓZ K))

/- Lemma 47.12.1 (2): the canonical map from the derived completion of `RΓ_Z(K)` to the
derived completion of `K` is an isomorphism in `D(A)`. -/
@[stacks 0A6W]
#check (@CategoryTheory.DerivedCategory.LocalCohomology.Completion.derivedCompletionCounitIsIso :
  ∀ {A : Type u} [CommRing A] (I : Ideal A) (hI : I.FG)
    (RΓZ : DerivedCategory (ModuleCat A) ⥤
      CategoryTheory.DerivedCategory.IdealPowerTorsion I)
    (hRΓZ : CategoryTheory.DerivedCategory.IdealPowerTorsion.inclusion I ⊣ RΓZ)
    (K : DerivedCategory (ModuleCat A)),
    IsIso (CategoryTheory.DerivedCategory.LocalCohomology.Completion.derivedCompletionCounit
      I hI RΓZ hRΓZ K))
