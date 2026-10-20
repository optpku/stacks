/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Localization
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.FiniteCoextension
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Polynomial
public import Mathlib.RingTheory.Localization.Submodule

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IsDualizingComplex

/-- An essentially finite type algebra over a Noetherian commutative ring with a dualizing
complex itself admits a dualizing complex. -/
theorem exists_of_essFiniteType
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Algebra.EssFiniteType A B]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} B))]
    (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (HB : MonoidalClosed (DerivedCategory (ModuleCat.{u} B)))
    (hA : ∃ ω : DerivedCategory (ModuleCat.{u} A), ω.IsDualizingComplex HA) :
    -- Local instance justification (search instability): `A` is underdetermined by the target.
    letI : IsNoetherianRing B := Algebra.EssFiniteType.isNoetherianRing A B
    ∃ η : DerivedCategory (ModuleCat.{u} B), η.IsDualizingComplex HB := sorry

end CategoryTheory.DerivedCategory.IsDualizingComplex
