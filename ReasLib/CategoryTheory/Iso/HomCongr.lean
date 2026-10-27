/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.HomCongr

/-!
# Isomorphisms and transport of invertible morphisms

This module records the categorical properties of `Iso.homCongr` that are
independent of any additive or fibred structure.
-/

@[expose] public section

universe u v

namespace CategoryTheory.Iso

variable {C : Type u} [Category.{v} C]

/-- Transporting a morphism along isomorphisms at its source and target
preserves and reflects invertibility. -/
theorem isIso_homCongr_iff
    {X Y X' Y' : C} (eX : X ≅ X') (eY : Y ≅ Y') (f : X ⟶ Y) :
    IsIso (eX.homCongr eY f) ↔ IsIso f := by
  constructor
  · intro h
    -- Local instance justification (proof-local temporary data): `h` is the invertibility
    -- certificate for the transported morphism used by the implication proof.
    letI : IsIso (eX.homCongr eY f) := h
    rw [show f = eX.hom ≫ eX.homCongr eY f ≫ eY.inv by simp]
    infer_instance
  · intro h
    -- Local instance justification (proof-local temporary data): `h` is the invertibility
    -- certificate for the original morphism used by the reverse implication proof.
    letI : IsIso f := h
    change IsIso (eX.inv ≫ f ≫ eY.hom)
    infer_instance

end CategoryTheory.Iso
