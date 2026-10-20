/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Discrete.Basic

/-!
# Equivalence criteria for functors between discrete categories

A functor between discrete categories is an equivalence if and only if it is bijective on
objects. This is a fundamental simplification: in discrete categories all hom-sets are
subsingletons, so faithfulness and fullness are automatic from bijectivity.

## Main declarations

* `CategoryTheory.Functor.isEquivalence_iff_bijective_of_isDiscrete` — the equivalence criterion.
-/

@[expose] public section

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

variable {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]

namespace Functor

/-- A functor between discrete categories is an equivalence iff it is bijective on objects.
In discrete categories all hom-sets are subsingletons, so faithfulness and fullness are
automatic. -/
theorem isEquivalence_iff_bijective_of_isDiscrete
    [IsDiscrete A] [IsDiscrete B] (G : A ⥤ B) :
    G.IsEquivalence ↔ Function.Bijective G.obj := by
  constructor
  · intro h
    exact ⟨fun X Y hXY ↦ obj_ext_of_isDiscrete (G.preimage (eqToHom hXY)),
           fun Y ↦ by
             rcases (Functor.EssSurj.mem_essImage (F := G) Y) with ⟨X, ⟨e⟩⟩
             exact ⟨X, obj_ext_of_isDiscrete e.hom⟩⟩
  · intro ⟨hinj, hsurj⟩
    exact
      { full := ⟨fun {X Y} f ↦
          ⟨eqToHom (hinj (obj_ext_of_isDiscrete f)), Subsingleton.elim _ _⟩⟩
        essSurj := Functor.essSurj_of_surj hsurj }

/-- A functor from a discrete category is faithful (all source hom-sets are subsingletons). -/
instance faithful_of_isDiscrete_source [IsDiscrete A] (G : A ⥤ B) : G.Faithful where
  map_injective := fun _ ↦ Subsingleton.elim _ _

/-- A faithful functor into a thin category reflects thinness. -/
theorem isThin_of_faithful (G : A ⥤ B) [G.Faithful] [Quiver.IsThin B] :
    Quiver.IsThin A :=
  fun _ _ ↦ ⟨fun f g ↦ G.map_injective (Subsingleton.elim _ _)⟩

end Functor

end CategoryTheory
