/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Normalized
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.FiniteCoextension
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex

/-- Derived coextension along a finite local homomorphism of Noetherian local commutative rings
carries a normalized dualizing complex over the source to one over the target. -/
theorem coextensionOfFiniteLocal
    {A B : Type u} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsLocalRing A] [IsLocalRing B]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} B))]
    (f : A →+* B) [IsLocalHom f] (hfinite : f.Finite)
    (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (HB : MonoidalClosed (DerivedCategory (ModuleCat.{u} B)))
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : ω.IsNormalizedDualizingComplex HA) :
    ((ModuleCat.derivedCoextensionOfScalars f).obj ω).IsNormalizedDualizingComplex HB := sorry

/-- Derived coextension along a surjective homomorphism of Noetherian local commutative rings
carries a normalized dualizing complex over the source to one over the target. -/
theorem coextensionOfSurjective
    {A B : Type u} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsLocalRing A] [IsLocalRing B]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} B))]
    (f : A →+* B) (hf : Function.Surjective f)
    (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (HB : MonoidalClosed (DerivedCategory (ModuleCat.{u} B)))
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : ω.IsNormalizedDualizingComplex HA) :
    ((ModuleCat.derivedCoextensionOfScalars f).obj ω).IsNormalizedDualizingComplex HB := sorry

end CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex
