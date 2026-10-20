/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Pseudofunctor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Object and `1`-cell computations for the based-inertia pseudofunctor

This leaf identifies the packaged object and `1`-cell actions with their canonical based-inertia
owners, including the objectwise and underlying-arrow readouts.
-/

@[expose] public section

universe u v u₁ v₁

namespace CategoryTheory
namespace BasedCategory

open BasedCategory BasedFunctor BasedNatIso BasedNatTrans
open Bicategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace Inertia

/-- The ordinary based-inertia pseudofunctor sends an object to its inertia category. -/
@[simp, stacks 04Z4 "based inertia pseudofunctor object computation"]
theorem pseudofunctor.obj (X : BasedCategory.{v₁, u₁} C) :
    (pseudofunctor C).obj X = inertia X := sorry

/-- The ordinary pseudofunctor `1`-cell action is the canonical inertia map. -/
@[simp, stacks 04Z4 "based inertia pseudofunctor map computation"]
theorem pseudofunctor.map {X Y : BasedCategory.{v₁, u₁} C} (F : X ⥤ᵇ Y) :
    (pseudofunctor C).map F = Inertia.map F := sorry

/-- Forgetting the packaged `1`-cell action recovers the underlying functor of the canonical
based-inertia map. -/
@[simp, stacks 04Z4 "based inertia pseudofunctor total computation"]
theorem pseudofunctor.map.toFunctor
    {X Y : BasedCategory.{v₁, u₁} C} (F : X ⥤ᵇ Y) :
    ((pseudofunctor C).map F).toFunctor = (Inertia.map F).toFunctor := sorry

/-- The object underlying the image of an inertia object is the image of its underlying object. -/
@[simp, stacks 04Z4 "based inertia pseudofunctor object readout"]
theorem pseudofunctor.map.obj.underlying
    {X Y : BasedCategory.{v₁, u₁} C} (F : X ⥤ᵇ Y) (A : (inertia X).obj) :
    (((pseudofunctor C).map F).toFunctor.obj A).obj =
      F.toFunctor.obj A.obj := sorry

/-- The automorphism of a packaged image is the image of the original automorphism. -/
@[simp, stacks 04Z4 "based inertia pseudofunctor automorphism readout"]
theorem pseudofunctor.map.obj.aut
    {X Y : BasedCategory.{v₁, u₁} C} (F : X ⥤ᵇ Y) (A : (inertia X).obj) :
    (((pseudofunctor C).map F).toFunctor.obj A).aut =
      F.toFunctor.mapIso A.aut := sorry

/-- The ambient arrow underlying the image of an inertia morphism is the image of its
underlying arrow. -/
@[simp, stacks 04Z4 "based inertia pseudofunctor arrow readout"]
theorem pseudofunctor.map.hom.underlying
    {X Y : BasedCategory.{v₁, u₁} C} (F : X ⥤ᵇ Y)
    {A B : (inertia X).obj} (φ : A ⟶ B) :
    CategoryTheory.RelativeInertia.hom (((pseudofunctor C).map F).toFunctor.map φ) =
      F.toFunctor.map (CategoryTheory.RelativeInertia.hom φ) := sorry

/-- Ordinary based inertia preserves identity `1`-morphisms on the nose. -/
@[simp, stacks 04Z4 "based inertia pseudofunctor identity"]
theorem pseudofunctor.map_id (X : BasedCategory.{v₁, u₁} C) :
    (pseudofunctor C).map (𝟭 X) = 𝟭 ((pseudofunctor C).obj X) := sorry

/-- Ordinary based inertia preserves composition of `1`-morphisms on the nose. -/
@[simp, stacks 04Z4 "based inertia pseudofunctor composition"]
theorem pseudofunctor.map_comp
    {X Y Z : BasedCategory.{v₁, u₁} C}
    (F : X ⥤ᵇ Y) (G : Y ⥤ᵇ Z) :
    (pseudofunctor C).map (F ⋙ G) =
      (pseudofunctor C).map F ⋙ (pseudofunctor C).map G := sorry

end Inertia

end BasedCategory
end CategoryTheory
