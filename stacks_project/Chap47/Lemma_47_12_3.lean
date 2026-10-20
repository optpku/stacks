/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.InternalHom
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 47.12.3: for objects `K` and `L` in `D(A)`, the canonical comparison from
`RHom_A(K^∧, L^∧)` to `RHom_A(RΓ_Z(K), RΓ_Z(L))` is an isomorphism in `D(A)`. -/
@[stacks 0A6Y]
#check (@CategoryTheory.DerivedCategory.LocalCohomology.rHomComparisonIsIso :
  ∀ {A : Type u} [CommRing A] (I : Ideal A) (hI : I.FG)
    (RΓZ : DerivedCategory (ModuleCat A) ⥤
      CategoryTheory.DerivedCategory.IdealPowerTorsion I)
    (hRΓZ : CategoryTheory.DerivedCategory.IdealPowerTorsion.inclusion I ⊣ RΓZ)
    (K L : DerivedCategory (ModuleCat A)),
    IsIso
      (CategoryTheory.DerivedCategory.LocalCohomology.rHomComparison
          I hI RΓZ hRΓZ K L :
        CategoryTheory.DerivedCategory.InternalHom.RHom.obj
            (DerivedCategory.derivedCompletionOf I hI K)
            (DerivedCategory.derivedCompletionOf I hI L) ⟶
          CategoryTheory.DerivedCategory.InternalHom.RHom.obj
            (RΓZ.obj K).obj (RΓZ.obj L).obj))
