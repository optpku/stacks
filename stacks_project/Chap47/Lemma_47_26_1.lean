/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.FaithfullyFlat
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

/- Lemma 47.26.1: canonical dualizing descends along a faithfully flat map between
Noetherian rings. -/
@[stacks 0E4A] #check
  (CategoryTheory.DerivedCategory.IsDualizingComplex.of_faithfullyFlat :
    ∀ {A B : Type u} [CommRing A] [CommRing B]
      [IsNoetherianRing A] [IsNoetherianRing B]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} B))]
      (f : A →+* B), f.FaithfullyFlat →
      (CA : CategoryTheory.DerivedCategory.CanonicalClosedPresentation (A := A)) →
      (CB : CategoryTheory.DerivedCategory.CanonicalClosedPresentation (A := B)) →
      (K : DerivedCategory (ModuleCat.{u} A)) →
      ((ModuleCat.derivedExtensionOfScalars f).obj K).IsCanonicalDualizingComplex CB →
      K.IsCanonicalDualizingComplex CA)
