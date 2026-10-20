/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.LocalizationAway
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

/- Lemma 47.15.7: a complex over a Noetherian commutative ring is dualizing if it is
dualizing after localization at every member of a finite family generating the unit ideal. -/
@[stacks 0A7H]
#check (CategoryTheory.DerivedCategory.IsDualizingComplex.of_localizationAway_unitIdeal :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    {ι : Type v} [Finite ι]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (f : ι → A) (hunit : Ideal.span (Set.range f) = ⊤)
    [∀ i, MonoidalCategory
      (DerivedCategory (ModuleCat.{u} (Localization.Away (f i))))]
    (Hlocal : ∀ i, MonoidalClosed
      (DerivedCategory (ModuleCat.{u} (Localization.Away (f i)))))
    (ω : DerivedCategory (ModuleCat.{u} A)),
    (∀ i,
      ((ModuleCat.derivedExtensionOfScalars
        (algebraMap A (Localization.Away (f i)))).obj ω).IsDualizingComplex (Hlocal i)) →
      ω.IsDualizingComplex HA)
