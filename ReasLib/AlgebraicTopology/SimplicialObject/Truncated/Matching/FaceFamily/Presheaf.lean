/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Matching.FaceFamily
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The presheaf of compatible face families

This file packages compatible face families as a presheaf on the coefficient category and records
its functoriality in the truncated simplicial object.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped Simplicial SimplexCategory.Truncated

universe u v

namespace CategoryTheory.SimplicialObject.Truncated.matching

variable {C : Type u} [Category.{v} C]

namespace FaceFamily

variable {n : ℕ} {U V W : SimplicialObject.Truncated C n}

/-- Precomposition along a morphism of test objects, bundled as the morphism used by the
face-family presheaf. -/
@[stacks 0186 "face-family presheaf precomposition map"]
def precompHom (U : SimplicialObject.Truncated C n) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    FaceFamily U X.unop ⟶ FaceFamily U Y.unop :=
  ↾fun F : FaceFamily U X.unop ↦ F.precomp f.unop

/-- The bundled precomposition map associated to an identity is the identity. -/
@[stacks 0186 "face-family presheaf precomposition identity"]
theorem precompHom_id (U : SimplicialObject.Truncated C n) (T : Cᵒᵖ) :
    precompHom U (𝟙 T) = 𝟙 (FaceFamily U T.unop) := sorry

/-- Bundled precomposition maps preserve composition. -/
@[stacks 0186 "face-family presheaf precomposition composition"]
theorem precompHom_comp (U : SimplicialObject.Truncated C n)
    {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    precompHom U (f ≫ g) = precompHom U f ≫ precompHom U g := sorry

/-- The presheaf of explicit matching face families associated to a truncated simplicial object. -/
@[stacks 0186 "explicit matching face-family presheaf"]
def presheaf (U : SimplicialObject.Truncated C n) : Cᵒᵖ ⥤ Type v where
  obj T := FaceFamily U T.unop
  map f := precompHom U f
  map_id T := precompHom_id U T
  map_comp f g := precompHom_comp U f g

/-- The explicit face-family presheaf evaluates to face families with the given test object. -/
@[simp, stacks 0186 "explicit face-family presheaf object"]
theorem presheaf_obj (U : SimplicialObject.Truncated C n) (T : C) :
    (presheaf U).obj (op T) = FaceFamily U T := sorry

/-- The action of the explicit face-family presheaf is precomposition. -/
@[simp, stacks 0186 "explicit face-family presheaf map"]
theorem presheaf_map (U : SimplicialObject.Truncated C n) {X Y : Cᵒᵖ}
    (f : X ⟶ Y) (F : FaceFamily U X.unop) :
    (presheaf U).map f F = F.precomp f.unop := sorry

/-- The component of the face-family presheaf map induced by a truncated simplicial morphism. -/
@[stacks 0186 "explicit matching face-family presheaf-map component"]
def presheafMapApp (α : U ⟶ V) (T : Cᵒᵖ) :
    (presheaf U).obj T ⟶ (presheaf V).obj T :=
  ↾fun F : FaceFamily U T.unop ↦ F.map α

/-- The component functions of a face-family presheaf map are natural in the test object. -/
@[stacks 0186 "explicit matching face-family presheaf-map naturality"]
theorem presheafMapApp.naturality (α : U ⟶ V)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (presheaf U).map f ≫ presheafMapApp α Y =
      presheafMapApp α X ≫ (presheaf V).map f := sorry

/-- A morphism of truncated simplicial objects induces a natural transformation between their
explicit matching face-family presheaves. -/
@[stacks 0186 "explicit matching face-family presheaf map"]
def presheafMap (α : U ⟶ V) : presheaf U ⟶ presheaf V where
  app := presheafMapApp α
  naturality := fun {X Y} f ↦ presheafMapApp.naturality α (X := X) (Y := Y) f

/-- The natural transformation induced on face-family presheaves acts by coordinatewise mapping. -/
@[simp, stacks 0186 "explicit face-family presheaf-map component"]
theorem presheafMap_app (α : U ⟶ V) (T : Cᵒᵖ) (F : FaceFamily U T.unop) :
    (presheafMap α).app T F = F.map α := sorry

/-- The face-family presheaf map associated to an identity is the identity natural
transformation. -/
@[simp, stacks 0186 "explicit face-family presheaf-map identity"]
theorem presheafMap.id (U : SimplicialObject.Truncated C n) :
    presheafMap (𝟙 U) = 𝟙 (presheaf U) := sorry

/-- Face-family presheaf maps preserve composition. -/
@[simp, stacks 0186 "explicit face-family presheaf-map composition"]
theorem presheafMap.comp (α : U ⟶ V) (β : V ⟶ W) :
    presheafMap (α ≫ β) = presheafMap α ≫ presheafMap β := sorry

namespace presheaf

/-- Explicit matching face families form a functor from truncated simplicial objects to
presheaves on the coefficient category. -/
@[stacks 0186 "face-family presheaf functor"]
def functor (level : ℕ) :
    SimplicialObject.Truncated C level ⥤ (Cᵒᵖ ⥤ Type v) where
  obj U := FaceFamily.presheaf U
  map α := FaceFamily.presheafMap α
  map_id U := FaceFamily.presheafMap.id U
  map_comp α β := FaceFamily.presheafMap.comp α β

/-- The face-family presheaf functor sends `U` to its explicit face-family presheaf. -/
@[simp, stacks 0186 "face-family presheaf functor object"]
theorem functor_obj (level : ℕ) (U : SimplicialObject.Truncated C level) :
    (functor (C := C) level).obj U = FaceFamily.presheaf U := sorry

/-- The face-family presheaf functor sends a truncated simplicial map to the coordinatewise
presheaf map. -/
@[simp, stacks 0186 "face-family presheaf functor map"]
theorem functor_map (level : ℕ) {U V : SimplicialObject.Truncated C level} (α : U ⟶ V) :
    (functor (C := C) level).map α = FaceFamily.presheafMap α := sorry

end presheaf

end FaceFamily
end CategoryTheory.SimplicialObject.Truncated.matching
