/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Inertia.Functoriality.Strict.LocalAction

/-!
# Strict inertia action computations

This leaf exposes the strict pseudofunctor's object, `1`-cell, and `2`-cell projections.
-/

@[expose] public section

open CategoryTheory
open Bicategory
open scoped Bicategory

universe u v

namespace CategoryTheory
namespace Inertia

/-- Forgetting the Cat wrapper from the strict `1`-cell action recovers the induced inertia
functor. -/
@[simp]
theorem strictPseudofunctor.map.toFunctor {C D : Cat.{v, u}} (F : C ⟶ D) :
    ((strictPseudofunctor).map F).toFunctor = Inertia.map F.toFunctor := sorry

/-- The object underlying the strict image of an inertia object is the image of its underlying
object. -/
@[simp]
theorem strictPseudofunctor.map.obj.underlying
    {C D : Cat.{v, u}} (F : C ⟶ D) (X : Inertia C) :
    (((strictPseudofunctor).map F).toFunctor.obj X).obj =
      F.toFunctor.obj X.obj := sorry

/-- The automorphism of a strict image is the image of the original automorphism. -/
@[simp]
theorem strictPseudofunctor.map.obj.aut
    {C D : Cat.{v, u}} (F : C ⟶ D) (X : Inertia C) :
    (((strictPseudofunctor).map F).toFunctor.obj X).aut =
      F.toFunctor.mapIso X.aut := sorry

/-- The arrow underlying a strict image morphism is the image of its underlying arrow. -/
@[simp]
theorem strictPseudofunctor.map.hom.underlying
    {C D : Cat.{v, u}} (F : C ⟶ D) {X Y : Inertia C} (f : X ⟶ Y) :
    Inertia.hom (((strictPseudofunctor).map F).toFunctor.map f) =
      F.toFunctor.map (Inertia.hom f) := sorry

/-- The `2`-cell action of the strict inertia pseudofunctor is the bundled induced inertia
transformation. -/
@[simp]
theorem strictPseudofunctor.map₂
    {C D : Cat.{v, u}} {F G : C ⟶ D} (η : F ⟶ G) :
    strictPseudofunctor.map₂ η =
      (Inertia.map₂ η.toNatTrans).toCatHom₂ := sorry

/-- Forgetting the Cat wrapper from the strict `2`-cell action recovers the induced natural
transformation. -/
@[simp]
theorem strictPseudofunctor.map₂.toNatTrans
    {C D : Cat.{v, u}} {F G : C ⟶ D} (η : F ⟶ G) :
    ((strictPseudofunctor).map₂ η).toNatTrans =
      Inertia.map₂ η.toNatTrans := sorry

/-- The component of the strict inertia `2`-cell action is the canonical intertwined component. -/
@[simp]
theorem strictPseudofunctor.map₂.app
    {C D : Cat.{v, u}} {F G : C ⟶ D} (η : F ⟶ G) (X : Inertia C) :
    ((strictPseudofunctor).map₂ η).toNatTrans.app X =
      Inertia.map₂.component η.toNatTrans X := sorry

/-- The ambient arrow underlying a strict inertia `2`-cell component is the original component. -/
@[simp]
theorem strictPseudofunctor.map₂.app.underlying
    {C D : Cat.{v, u}} {F G : C ⟶ D} (η : F ⟶ G) (X : Inertia C) :
    Inertia.hom (((strictPseudofunctor).map₂ η).toNatTrans.app X) =
      η.toNatTrans.app X.obj := sorry

/-- The strict inertia `2`-cell action is natural in inertia morphisms. -/
@[reassoc]
theorem strictPseudofunctor.map₂.naturality
    {C D : Cat.{v, u}} {F G : C ⟶ D} (η : F ⟶ G)
    {X Y : Inertia C} (f : X ⟶ Y) :
    ((strictPseudofunctor).map F).toFunctor.map f ≫
        ((strictPseudofunctor).map₂ η).toNatTrans.app Y =
      ((strictPseudofunctor).map₂ η).toNatTrans.app X ≫
        ((strictPseudofunctor).map G).toFunctor.map f := sorry

/-- Two strict inertia `2`-cell images agree when all of their inertia components agree. -/
theorem strictPseudofunctor.map₂.ext
    {C D : Cat.{v, u}} {F G : C ⟶ D} {η θ : F ⟶ G}
    (h : ∀ X : Inertia C,
      ((strictPseudofunctor).map₂ η).toNatTrans.app X =
        ((strictPseudofunctor).map₂ θ).toNatTrans.app X) :
    (strictPseudofunctor).map₂ η = (strictPseudofunctor).map₂ θ := sorry

end Inertia
end CategoryTheory
