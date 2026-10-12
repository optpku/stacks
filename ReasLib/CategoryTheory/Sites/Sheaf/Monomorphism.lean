/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import ReasLib.CategoryTheory.Presheaf.MonoEpi

/-!
# Monomorphisms of sheaves

This module records the sectionwise injectivity criterion for morphisms of
Type-valued sheaves.
-/

@[expose] public section

open CategoryTheory Opposite

universe u v w

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- A morphism of `Type`-valued sheaves is monic exactly when it is injective on
sections over every object of the site. -/
theorem mono_iff_app_injective_type {F G : Sheaf J (Type w)} (φ : F ⟶ G) :
    Mono φ ↔ ∀ U : C, Function.Injective (φ.hom.app (op U)) := sorry

end CategoryTheory.Sheaf
