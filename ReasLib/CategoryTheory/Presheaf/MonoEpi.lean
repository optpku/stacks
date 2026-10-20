/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Presheaf.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Objectwise mono and epi criteria for presheaves

This module records the reusable `Type`-valued presheaf criteria that categorical monomorphisms
and epimorphisms are respectively sectionwise injective and surjective.
-/

@[expose] public section

open Opposite

universe u v

namespace CategoryTheory.Presheaf

variable {C : Type u} [Category.{v} C]

/-- A morphism of `Type`-valued presheaves is monic exactly when it is injective on sections over
every object. -/
theorem mono_iff_injective {F G : Presheaf C} (φ : F ⟶ G) :
    Mono φ ↔ ∀ U : C, Function.Injective (φ.app (op U)) := sorry

/-- A morphism of `Type`-valued presheaves is epic exactly when it is surjective on sections over
every object. -/
theorem epi_iff_surjective {F G : Presheaf C} (φ : F ⟶ G) :
    Epi φ ↔ ∀ U : C, Function.Surjective (φ.app (op U)) := sorry

/-- A morphism of `Type`-valued presheaves is an isomorphism exactly when it is sectionwise
injective and surjective. -/
theorem isIso_iff_injective_and_surjective {F G : Presheaf C} (φ : F ⟶ G) :
    IsIso φ ↔
      (∀ U : C, Function.Injective (φ.app (op U))) ∧
        ∀ U : C, Function.Surjective (φ.app (op U)) := sorry

end CategoryTheory.Presheaf
