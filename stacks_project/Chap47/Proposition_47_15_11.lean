/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.EssentiallyFiniteType
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

/- Proposition 47.15.11: if a Noetherian commutative ring has a dualizing complex,
then every essentially finite type algebra over it has a dualizing complex. -/
@[stacks 0A7K] #check
  (CategoryTheory.DerivedCategory.IsDualizingComplex.exists_of_essFiniteType : ∀ {A B : Type u}
    [CommRing A] [CommRing B] [Algebra A B]
      [IsNoetherianRing A] [Algebra.EssFiniteType A B]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} B))]
      (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
      (HB : MonoidalClosed (DerivedCategory (ModuleCat.{u} B)))
      (hA : ∃ ω : DerivedCategory (ModuleCat.{u} A), ω.IsDualizingComplex HA),
      letI : IsNoetherianRing B := Algebra.EssFiniteType.isNoetherianRing A B
      ∃ η : DerivedCategory (ModuleCat.{u} B), η.IsDualizingComplex HB)
