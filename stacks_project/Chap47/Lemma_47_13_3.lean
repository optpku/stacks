/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Coextension.RHom
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open DerivedCategory.InternalHom

noncomputable section

universe u

namespace CategoryTheory.ModuleCat

variable {A B : Type u} [CommRing A] [CommRing B]

/- Lemma 47.13.3: Let `φ : A → B` be a ring homomorphism. Restricting the derived coextension
`RHom_A(B, K)` to `A` identifies it with canonical derived `RHom` over `A`; degreewise this
gives the corresponding `Ext` identification. -/
@[stacks 0A71] #check
  (CategoryTheory.ModuleCat.DerivedCoextension.restrictionIsomorphicRHom :
    ∀ {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
      (K : DerivedCategory (ModuleCat A)),
      IsIsomorphic
        ((derivedRestrictionOfScalars f).obj ((derivedCoextensionOfScalars f).obj K))
        (RHom.obj
          (single0 ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B))) K))

#check
  (CategoryTheory.ModuleCat.DerivedCoextension.homologyRestrictionIsomorphicRHom :
    ∀ {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
      (K : DerivedCategory (ModuleCat A)) (q : ℤ),
      IsIsomorphic
        ((ModuleCat.restrictScalars f).obj
          ((DerivedCategory.homologyFunctor (ModuleCat B) q).obj
            ((derivedCoextensionOfScalars f).obj K)))
        ((DerivedCategory.homologyFunctor (ModuleCat A) q).obj
          (RHom.obj
            (single0 ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B))) K)))

end CategoryTheory.ModuleCat
