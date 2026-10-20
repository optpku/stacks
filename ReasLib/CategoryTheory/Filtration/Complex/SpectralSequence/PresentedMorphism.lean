/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.SpectralSequence.Presentation

/-!
# Morphisms of Presented Spectral Sequences

This file records when a spectral-sequence morphism is induced pagewise by a filtered-complex
morphism relative to chosen explicit page presentations.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace FilteredComplex

namespace Page.Presentation.Map

/-- A spectral-sequence morphism is induced pagewise by a filtered-complex morphism relative to
chosen explicit `Zᵣ/Bᵣ` presentations. This is stronger than association compatibility: it
records the quotient description of every finite-page component. -/
@[stacks 012O "pagewise induced morphism of presented spectral sequences"]
def IsInduced {K L : FilteredComplex C}
    {E E' : CohomologicalSpectralSequence C 0}
    (A : Page.Presentation K E) (B : Page.Presentation L E')
    (α : K ⟶ L) (φ : E ⟶ E') : Prop :=
  ∀ (r : ℕ) (n p : ℤ),
    Page.Map.IsInduced α r n p
      (Page.Representative.transport A.pageIso B.pageIso φ r n p)

namespace IsInduced

/-- The identity map of a presented spectral sequence is pagewise induced by the identity map
of its filtered complex. -/
@[stacks 012O "identity map of presented spectral sequences"]
theorem id {K : FilteredComplex C} {E : CohomologicalSpectralSequence C 0}
    (A : Page.Presentation K E) :
    Page.Presentation.Map.IsInduced A A (𝟙 K) (𝟙 E) := sorry

/-- Pagewise induced maps between presented spectral sequences are closed under composition. -/
@[stacks 012O "composition of presented spectral-sequence maps"]
theorem comp {K L M : FilteredComplex C}
    {E E' E'' : CohomologicalSpectralSequence C 0}
    (A : Page.Presentation K E) (B : Page.Presentation L E')
    (D : Page.Presentation M E'')
    {α : K ⟶ L} {β : L ⟶ M} {φ : E ⟶ E'} {ψ : E' ⟶ E''}
    (hφ : Page.Presentation.Map.IsInduced A B α φ)
    (hψ : Page.Presentation.Map.IsInduced B D β ψ) :
    Page.Presentation.Map.IsInduced A D (α ≫ β) (φ ≫ ψ) := sorry

/-- Two morphisms of presented spectral sequences induced by the same filtered-complex morphism
are equal. -/
@[stacks 012O "extensionality of induced presented spectral-sequence morphisms"]
theorem hom_ext {K L : FilteredComplex C}
    {E E' : CohomologicalSpectralSequence C 0}
    (A : Page.Presentation K E) (B : Page.Presentation L E')
    {α : K ⟶ L} {φ ψ : E ⟶ E'}
    (hφ : Page.Presentation.Map.IsInduced A B α φ)
    (hψ : Page.Presentation.Map.IsInduced A B α ψ) :
    φ = ψ := sorry

end IsInduced

end Page.Presentation.Map

end FilteredComplex

end CategoryTheory
