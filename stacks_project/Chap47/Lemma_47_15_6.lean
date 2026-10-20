/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Localization
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped DerivedTensorWithAlgebra

noncomputable section

universe u

/- Lemma 47.15.6: derived extension of a dualizing complex over a Noetherian commutative
ring `A` to `Localization S` is a dualizing complex over `Localization S`. -/
@[stacks 0A7G]
#check (CategoryTheory.DerivedCategory.IsDualizingComplex.localization :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (S : Submonoid A)
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} (Localization S)))]
    (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (HB : MonoidalClosed (DerivedCategory (ModuleCat.{u} (Localization S))))
    (ω : DerivedCategory (ModuleCat.{u} A)),
    ω.IsDualizingComplex HA → (ω ⊗[A]^L[Localization S]).IsDualizingComplex HB)
