/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Functor.KanExtension.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Transitivity of right Kan extensions

Right Kan extensions paste and cancel along composites of functors. This module supplies the
right-handed counterpart of Mathlib's `LeftExtension.precomp₂` API, at the level of extension
objects and their universal properties.
-/

@[expose] public section

open CategoryTheory

universe vC uC vD uD vD' uD' vH uH

namespace CategoryTheory.Functor

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {D' : Type uD'} [Category.{vD'} D']
variable {H : Type uH} [Category.{vH} H]

/-- Precompose a right extension along `L'` by `L`, then paste its counit with the right
extension counit `α` along `L`. -/
@[simps!, stacks 002L "pasting functor for right extensions"]
def RightExtension.precomp₂
    {F₀ : C ⥤ H} {L : C ⥤ D} {F₁ : D ⥤ H} (L' : D ⥤ D')
    (α : L ⋙ F₁ ⟶ F₀) :
    L'.RightExtension F₁ ⥤ (L ⋙ L').RightExtension F₀ :=
  RightExtension.precomp L' F₁ L ⋙ CostructuredArrow.map α

variable {L : C ⥤ D} {L' : D ⥤ D'}
variable {F₀ : C ⥤ H} {F₁ : D ⥤ H} {F₂ : D' ⥤ H}
variable (α : L ⋙ F₁ ⟶ F₀)

namespace RightExtension.precomp₂

/-- The canonical instance form of right Kan extension pasting. The `precomp₂` namespace
keeps the downstream name short while retaining the full mathematical owner. -/
@[stacks 002L "canonical instance for pasting right Kan extensions"]
instance isKan
    [F₁.IsRightKanExtension α] {b : L'.RightExtension F₁}
    [b.left.IsRightKanExtension b.hom] :
    ((RightExtension.precomp₂ L' α).obj b).left.IsRightKanExtension
      ((RightExtension.precomp₂ L' α).obj b).hom := sorry

/-- Cancel the first right Kan extension from a pasted right Kan extension. This remains an
explicit theorem rather than an instance, avoiding a typeclass-search cycle with `isKan`. -/
@[stacks 002L "explicit cancellation for pasted right Kan extensions"]
theorem isKanOf
    [F₁.IsRightKanExtension α] {b : L'.RightExtension F₁}
    [((RightExtension.precomp₂ L' α).obj b).left.IsRightKanExtension
      ((RightExtension.precomp₂ L' α).obj b).hom] :
    b.left.IsRightKanExtension b.hom := sorry

/-- Under a right Kan extension along the first functor, universality before and after
`precomp₂` is equivalent. -/
@[stacks 002L "right Kan extension criterion in the precomp₂ namespace"]
theorem isKan_iff
    [F₁.IsRightKanExtension α] (b : L'.RightExtension F₁) :
    b.left.IsRightKanExtension b.hom ↔
      ((RightExtension.precomp₂ L' α).obj b).left.IsRightKanExtension
        ((RightExtension.precomp₂ L' α).obj b).hom := sorry

/-- Canonical pasting criterion after replacing the composite indexing functor by an
isomorphic functor. The pasted counit is displayed explicitly, so callers need not supply a
separate morphism and coherence proof. -/
@[stacks 002L "right Kan extension criterion with a canonical pasted counit"]
theorem isKan_iff_iso
    [F₁.IsRightKanExtension α]
    (L'' : C ⥤ D') (e : L ⋙ L' ≅ L'') (β : L' ⋙ F₂ ⟶ F₁) :
    F₂.IsRightKanExtension β ↔
      F₂.IsRightKanExtension
        (whiskerRight e.inv F₂ ≫
          (Functor.associator _ _ _).hom ≫ whiskerLeft L β ≫ α) := sorry

/-- Right Kan extension is stable under pasting and cancellation, allowing the composite
indexing functor to be replaced by a naturally isomorphic functor. -/
@[stacks 002L "right Kan extension pasting and cancellation"]
theorem isKan_iff_of_eq
    [F₁.IsRightKanExtension α]
    (L'' : C ⥤ D') (e : L ⋙ L' ≅ L'')
    (β : L' ⋙ F₂ ⟶ F₁) (γ : L'' ⋙ F₂ ⟶ F₀)
    (hγ : whiskerRight e.inv F₂ ≫
      (Functor.associator _ _ _).hom ≫ whiskerLeft L β ≫ α = γ) :
    F₂.IsRightKanExtension β ↔ F₂.IsRightKanExtension γ := sorry

end RightExtension.precomp₂

end CategoryTheory.Functor
