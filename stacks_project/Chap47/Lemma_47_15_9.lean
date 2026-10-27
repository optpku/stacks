/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.FiniteCoextension
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

/- Lemma 47.15.9: derived coextension along a surjective homomorphism preserves dualizing complexes. -/
@[stacks 0A7I] #check
  (CategoryTheory.DerivedCategory.IsDualizingComplex.coextensionOfSurjective :
    ∀ {A B : Type u} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} B))],
    (f : A →+* B) → Function.Surjective f →
    (CA : DerivedCategory.CanonicalClosedPresentation (A := A)) →
    (CB : DerivedCategory.CanonicalClosedPresentation (A := B)) →
    (ω : DerivedCategory (ModuleCat.{u} A)) →
    ω.IsCanonicalDualizingComplex CA →
    ((ModuleCat.derivedCoextensionOfScalars f).obj ω).IsCanonicalDualizingComplex CB)
