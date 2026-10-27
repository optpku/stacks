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

/- Lemma 47.15.8: derived coextension along a finite homomorphism of Noetherian
commutative rings sends a dualizing complex over the source to one over the target. -/
@[stacks 0AX0] #check
  (CategoryTheory.DerivedCategory.IsDualizingComplex.coextensionOfFinite :
    ∀ {A B : Type u} [CommRing A] [CommRing B]
      [IsNoetherianRing A] [IsNoetherianRing B]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} B))]
      (f : A →+* B) (hf : f.Finite)
      (CA : DerivedCategory.CanonicalClosedPresentation (A := A))
      (CB : DerivedCategory.CanonicalClosedPresentation (A := B))
      (ω : DerivedCategory (ModuleCat.{u} A))
      (hω : ω.IsCanonicalDualizingComplex CA),
      ((CategoryTheory.ModuleCat.derivedCoextensionOfScalars f).obj ω).IsCanonicalDualizingComplex CB)
