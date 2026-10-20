/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Iso
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Isomorphisms from Explicit Invertibility Certificates

This file provides a data-level bridge from an explicit `IsIso f` certificate to the
corresponding isomorphism. It avoids installing proof-local instances merely to use `asIso`.
@stack 0E1U
-/

@[expose] public section

noncomputable section

universe v u

namespace CategoryTheory.IsIso

variable {C : Type u} [Category.{v} C] {X Y : C} {f : X ⟶ Y}

/-- Reinterpret a morphism equipped with an explicit invertibility certificate as an
isomorphism. -/
@[stacks 0E1U "explicit isomorphism from an invertibility certificate"]
noncomputable def toIso (hf : IsIso f) : X ≅ Y :=
  @asIso C _ X Y f hf

/-- The forward morphism of the isomorphism attached to an explicit certificate is the
original morphism. -/
@[simp, stacks 0E1U "explicit isomorphism forward map"]
theorem toIso_hom (hf : IsIso f) : hf.toIso.hom = f := sorry

/-- The inverse morphism of the isomorphism attached to an explicit certificate is mathlib's
inverse computed using that certificate. -/
@[simp, stacks 0E1U "explicit isomorphism inverse map"]
theorem toIso_inv (hf : IsIso f) :
    hf.toIso.inv = @CategoryTheory.inv C _ X Y f hf := sorry

end CategoryTheory.IsIso
