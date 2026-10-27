/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Localization.Submodule
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IsDualizingComplex

/-- Derived scalar extension to a localization sends a dualizing complex over a Noetherian
commutative ring to a dualizing complex over the localized ring. -/
theorem localization
    {A : Type u} [CommRing A] [IsNoetherianRing A] (S : Submonoid A)
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} (Localization S)))]
    (CA : CanonicalClosedPresentation (A := A))
    (CB : CanonicalClosedPresentation (A := Localization S))
    (ω : DerivedCategory (ModuleCat.{u} A))
    (hω : ω.IsCanonicalDualizingComplex CA) :
    ((ModuleCat.derivedExtensionOfScalars
      (algebraMap A (Localization S))).obj ω).IsCanonicalDualizingComplex CB := sorry

end CategoryTheory.DerivedCategory.IsDualizingComplex
