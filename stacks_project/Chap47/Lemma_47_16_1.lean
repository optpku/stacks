/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Normalized.FiniteLocal
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex

/- Lemma 47.16.1: derived coextension along a finite local homomorphism of Noetherian local
commutative rings sends a normalized dualizing complex to a normalized dualizing complex. -/
@[stacks 0AX1] #check
  (CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex.coextensionOfFiniteLocal :
    ∀ {A B : Type u} [CommRing A] [CommRing B]
      [IsNoetherianRing A] [IsNoetherianRing B] [IsLocalRing A] [IsLocalRing B]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} B))]
      (f : A →+* B) [IsLocalHom f] (hfinite : f.Finite)
      (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
      (HB : MonoidalClosed (DerivedCategory (ModuleCat.{u} B)))
      (ω : DerivedCategory (ModuleCat.{u} A)) (hω : ω.IsNormalizedDualizingComplex HA),
      ((ModuleCat.derivedCoextensionOfScalars f).obj ω).IsNormalizedDualizingComplex HB)

end CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex
