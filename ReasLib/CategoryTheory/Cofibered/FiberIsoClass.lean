/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Types.Basic
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Fiber
public import ReasLib.CategoryTheory.Fibered.Cleavage.Basic.Reindex.Functor
public import ReasLib.CategoryTheory.Fibered.FiberIsoClassPresheaf.Basic
public import ReasLib.CategoryTheory.Functor.IsomorphismClasses
public import ReasLib.CategoryTheory.Cofibered.InGroupoids
public import ReasLib.CategoryTheory.Cofibered.Fiber

/-!
# Fiberwise isomorphism-class functors of cofibered categories

A category cofibered in groupoids `p : F ⥤ C` determines a covariant functor sending `U` to the
isomorphism classes of the fibre `p.Fiber U`, with action by pushforward. A morphism of cofibered
categories induces a natural transformation of these functors.
-/

@[expose] public section

universe u v uF vF

namespace CategoryTheory

open Opposite
open Functor Fiber
open scoped BasedFunctor

variable {C : Type u} [Category.{v} C]
variable {F : Type uF} [Category.{vF} F]

/-- Pushforward induces a map between the isomorphism classes of the standard fibres. -/
noncomputable def Functor.fiberIsoClassMap (p : F ⥤ C) [IsFibered.InGroupoids p.op]
    {U V : C} (f : U ⟶ V) :
    isomorphismClasses.obj (Cat.of (p.Fiber U)) ⟶
      isomorphismClasses.obj (Cat.of (p.Fiber V)) :=
  TypeCat.ofHom (Functor.pushforwardFiberFunctor p (Functor.cleavageOp p) f).isoClassesMap

/-- Pushforward on fibrewise isomorphism classes preserves the identity base arrow. -/
theorem Functor.fiberIsoClassMap.id (p : F ⥤ C) [IsFibered.InGroupoids p.op] (U : C) :
    Functor.fiberIsoClassMap p (𝟙 U) = 𝟙 (isomorphismClasses.obj (Cat.of (p.Fiber U))) := sorry

/-- Pushforward on fibrewise isomorphism classes preserves composition of base arrows. -/
theorem Functor.fiberIsoClassMap.comp (p : F ⥤ C) [IsFibered.InGroupoids p.op]
    {U V W : C} (f : U ⟶ V) (g : V ⟶ W) :
    Functor.fiberIsoClassMap p (f ≫ g) =
      Functor.fiberIsoClassMap p f ≫ Functor.fiberIsoClassMap p g := sorry

/-- The covariant functor of fibrewise isomorphism classes of a category cofibered in groupoids. -/
noncomputable def Functor.fiberIsoClassFunctor (p : F ⥤ C) [IsFibered.InGroupoids p.op] :
    C ⥤ Type uF where
  obj U := isomorphismClasses.obj (Cat.of (p.Fiber U))
  map := Functor.fiberIsoClassMap p
  map_id := Functor.fiberIsoClassMap.id p
  map_comp := Functor.fiberIsoClassMap.comp p

/-- The value of `fiberIsoClassFunctor p` at `U` is the type of isomorphism classes in the fibre
over `U`. -/
@[simp]
theorem Functor.fiberIsoClassFunctor.obj (p : F ⥤ C) [IsFibered.InGroupoids p.op] (U : C) :
    (Functor.fiberIsoClassFunctor p).obj U =
      isomorphismClasses.obj (Cat.of (p.Fiber U)) := sorry

/-- Represented classes in `fiberIsoClassFunctor p` match those in `fiberIsoClassPresheaf p.op`
after identifying `p.Fiber U` with the opposite fibre. -/
theorem Functor.fiberIsoClassFunctor.mk_iff_presheaf
    (p : F ⥤ C) [IsFibered.InGroupoids p.op] {U : C} (x y : p.Fiber U) :
    (Quotient.mk'' x : (Functor.fiberIsoClassFunctor p).obj U) = Quotient.mk'' y ↔
      (Quotient.mk'' (Functor.toOpFiber p x) :
          (Functor.fiberIsoClassPresheaf p.op).obj (op (op U))) =
        Quotient.mk'' (Functor.toOpFiber p y) := sorry

/-- Pushforward of a represented fibrewise isomorphism class may be computed using any cleavage. -/
theorem Functor.fiberIsoClassFunctor.map_mk
    (p : F ⥤ C) [IsFibered.InGroupoids p.op] (χ : p.op.Cleavage)
    {U V : C} (f : U ⟶ V) (x : p.Fiber U) :
    (Functor.fiberIsoClassFunctor p).map f (Quotient.mk'' x) =
      Quotient.mk'' (Functor.pushforwardFiberObj p χ f x) := sorry

variable {X Y : CofiberedCategoryOver.Groupoids.{u, v, uF, vF} C}

/-- A morphism of categories cofibered in groupoids induces a natural transformation of
fibrewise isomorphism-class functors. -/
noncomputable def CofiberedCategoryOver.Groupoids.fiberIsoClassFunctorMap (φ : X ⟶ Y) :
    Functor.fiberIsoClassFunctor X.p ⟶ Functor.fiberIsoClassFunctor Y.p where
  app U :=
    TypeCat.ofHom
      ((CofiberedCategoryOver.Groupoids.toBasedFunctor φ).fiberFunctor U).isoClassesMap
  naturality := sorry

/-- The component of `fiberIsoClassFunctorMap` at `U` is the map induced by the fibre functor. -/
theorem CofiberedCategoryOver.Groupoids.fiberIsoClassFunctorMap_app (φ : X ⟶ Y) (U : C) :
    (CofiberedCategoryOver.Groupoids.fiberIsoClassFunctorMap φ).app U =
      TypeCat.ofHom
        ((CofiberedCategoryOver.Groupoids.toBasedFunctor φ).fiberFunctor U).isoClassesMap := sorry

/-- On a represented fibre class, `fiberIsoClassFunctorMap` applies the induced fibre functor. -/
theorem CofiberedCategoryOver.Groupoids.fiberIsoClassFunctorMap_app_mk
    (φ : X ⟶ Y) (U : C) (x : X.p.Fiber U) :
    (CofiberedCategoryOver.Groupoids.fiberIsoClassFunctorMap φ).app U (Quotient.mk'' x) =
      Quotient.mk''
        (((CofiberedCategoryOver.Groupoids.toBasedFunctor φ).fiberFunctor U).obj x) := sorry

end CategoryTheory
