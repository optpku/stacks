/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Localization

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.DerivedCategory.IsDualizingComplex

/-- A complex over a Noetherian commutative ring is dualizing if it is dualizing after
localization at every member of a finite family generating the unit ideal. -/
theorem of_localizationAway_unitIdeal
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {ι : Type v} [Finite ι]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (CA : CanonicalClosedPresentation (A := A))
    (f : ι → A) (hunit : Ideal.span (Set.range f) = ⊤)
    [∀ i, MonoidalCategory
      (DerivedCategory (ModuleCat.{u} (Localization.Away (f i))))]
    (Clocal : ∀ i, CanonicalClosedPresentation
      (A := Localization.Away (f i)))
    (ω : DerivedCategory (ModuleCat.{u} A))
    (hlocal : ∀ i,
      ((ModuleCat.derivedExtensionOfScalars
        (algebraMap A (Localization.Away (f i)))).obj ω).IsCanonicalDualizingComplex (Clocal i)) :
    ω.IsCanonicalDualizingComplex CA := sorry

end CategoryTheory.DerivedCategory.IsDualizingComplex
