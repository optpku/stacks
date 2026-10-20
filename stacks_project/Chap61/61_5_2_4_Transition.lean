/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.WLocalHull.Transition

/-!
# Vanishing-pattern stage transitions

For finite `E₁ ⊆ E₂ ⊆ A`, the canonical stage map `A_{E₁} → A_{E₂}` induces an
affine scheme morphism `X_{E₂} ⟶ X_{E₁}` which sends `Z_{E₂}` into `Z_{E₁}`.
-/

@[expose] public section

open AlgebraicGeometry Algebra.WLocalHull CategoryTheory

universe u

#check (Algebra.WLocalHull.algHom :
  ∀ {A : Type u} [CommRing A] {E₁ E₂ : Finset A}, E₁ ⊆ E₂ →
    (stage A E₁ →ₐ[A] stage A E₂))

#check (Algebra.WLocalHull.spectrumMap :
  ∀ {A : Type u} [CommRing A] {E₁ E₂ : Finset A}, E₁ ⊆ E₂ →
    (spectrum A E₂ ⟶ spectrum A E₁))

#check (Algebra.WLocalHull.ringFunctor :
  ∀ (A : Type u) [CommRing A], Finset A ⥤ CommRingCat.{u})

#check (Algebra.WLocalHull.spectrumFunctor :
  ∀ (A : Type u) [CommRing A], (Finset A)ᵒᵖ ⥤ Scheme.{u})
