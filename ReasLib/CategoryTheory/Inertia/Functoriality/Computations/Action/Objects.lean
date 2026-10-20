/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Inertia.Functoriality.Pseudofunctor

/-!
# Object and `1`-cell computations for the ordinary inertia pseudofunctor

This leaf identifies the packaged object and `1`-cell actions with their canonical inertia
owners, including objectwise and underlying-arrow readouts.
-/

@[expose] public section

open CategoryTheory
open Bicategory
open scoped Bicategory

universe u v

namespace CategoryTheory
namespace Inertia

/-- The object action of the inertia pseudofunctor is the bundled inertia category. -/
@[simp, stacks 04Z4 "inertia pseudofunctor object action"]
theorem pseudofunctor.obj (C : Cat.{v, u}) :
    pseudofunctor.obj C = Cat.of (Inertia C) := sorry

/-- The `1`-cell action of the inertia pseudofunctor is the bundled induced inertia functor. -/
@[simp, stacks 04Z4 "inertia pseudofunctor one-cell action"]
theorem pseudofunctor.map {C D : Cat.{v, u}} (F : C ⟶ D) :
    pseudofunctor.map F = (Inertia.map F.toFunctor).toCatHom := sorry

/-- Forgetting the Cat wrapper from the `1`-cell action recovers the induced inertia functor. -/
@[simp, stacks 04Z4 "inertia pseudofunctor one-cell underlying functor"]
theorem pseudofunctor.map.toFunctor {C D : Cat.{v, u}} (F : C ⟶ D) :
    ((pseudofunctor).map F).toFunctor = Inertia.map F.toFunctor := sorry

/-- Evaluation of the `1`-cell action on an inertia object is evaluation of the induced inertia
functor. -/
@[simp, stacks 04Z4 "inertia pseudofunctor object readout"]
theorem pseudofunctor.map.obj
    {C D : Cat.{v, u}} (F : C ⟶ D) (X : Inertia C) :
    ((pseudofunctor).map F).toFunctor.obj X =
      (Inertia.map F.toFunctor).obj X := sorry

/-- The object underlying a pseudofunctor image is the image of the underlying object. -/
@[simp, stacks 04Z4 "inertia pseudofunctor underlying-object readout"]
theorem pseudofunctor.map.obj.underlying
    {C D : Cat.{v, u}} (F : C ⟶ D) (X : Inertia C) :
    (((pseudofunctor).map F).toFunctor.obj X).obj =
      F.toFunctor.obj X.obj := sorry

/-- The automorphism of a pseudofunctor image is the image of the original automorphism. -/
@[simp, stacks 04Z4 "inertia pseudofunctor automorphism readout"]
theorem pseudofunctor.map.obj.aut
    {C D : Cat.{v, u}} (F : C ⟶ D) (X : Inertia C) :
    (((pseudofunctor).map F).toFunctor.obj X).aut =
      F.toFunctor.mapIso X.aut := sorry

/-- Evaluation of the `1`-cell action on an inertia morphism is evaluation of the induced inertia
functor. -/
@[simp, stacks 04Z4 "inertia pseudofunctor arrow readout"]
theorem pseudofunctor.map.hom
    {C D : Cat.{v, u}} (F : C ⟶ D) {X Y : Inertia C} (f : X ⟶ Y) :
    ((pseudofunctor).map F).toFunctor.map f =
      (Inertia.map F.toFunctor).map f := sorry

/-- The arrow underlying a pseudofunctor image morphism is the image of its underlying arrow. -/
@[simp, stacks 04Z4 "inertia pseudofunctor underlying-arrow readout"]
theorem pseudofunctor.map.hom.underlying
    {C D : Cat.{v, u}} (F : C ⟶ D) {X Y : Inertia C} (f : X ⟶ Y) :
    Inertia.hom (((pseudofunctor).map F).toFunctor.map f) =
      F.toFunctor.map (Inertia.hom f) := sorry

/-- The ordinary inertia pseudofunctor preserves identity `1`-morphisms on the nose. -/
@[simp, stacks 04Z4 "inertia pseudofunctor identity action"]
theorem pseudofunctor.map_id (C : Cat.{v, u}) :
    (pseudofunctor).map (𝟙 C) = 𝟙 ((pseudofunctor).obj C) := sorry

/-- The ordinary inertia pseudofunctor preserves composition of `1`-morphisms on the nose. -/
@[simp, stacks 04Z4 "inertia pseudofunctor composition action"]
theorem pseudofunctor.map_comp
    {C D E : Cat.{v, u}} (F : C ⟶ D) (G : D ⟶ E) :
    (pseudofunctor).map (F ≫ G) =
      (pseudofunctor).map F ≫ (pseudofunctor).map G := sorry

end Inertia
end CategoryTheory
