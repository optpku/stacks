/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Cofibered.Pushforward

/-!
# Covariant action on fibres

Opposite-fibre conversion transports the reindexing action of a cleavage of `p.op` to
pushforward functors between the standard fibres of `p`.
-/

@[expose] public section

universe u v uF vF

namespace CategoryTheory

open Opposite
open Functor Fiber

variable {C : Type u} [Category.{v} C]
variable {F : Type uF} [Category.{vF} F]

/-- The object of `p.op.Fiber (op U)` corresponding to an object of `p.Fiber U`. -/
def Functor.toOpFiber (p : F ⥤ C) {U : C} (x : p.Fiber U) : p.op.Fiber (op U) :=
  ⟨op x.1, congrArg op x.property⟩

/-- The object of `p.Fiber U` corresponding to an object of `p.op.Fiber (op U)`. -/
def Functor.fromOpFiber (p : F ⥤ C) {U : C} (x : p.op.Fiber (op U)) : p.Fiber U :=
  ⟨unop x.1, congrArg unop x.property⟩

/-- Converting a fibre object to the opposite fibre and back recovers the object. -/
@[simp]
theorem Functor.fromOpFiber_toOpFiber (p : F ⥤ C) {U : C} (x : p.Fiber U) :
    Functor.fromOpFiber p (Functor.toOpFiber p x) = x := sorry

/-- Converting an opposite-fibre object to a standard fibre and back recovers the object. -/
@[simp]
theorem Functor.toOpFiber_fromOpFiber (p : F ⥤ C) {U : C} (x : p.op.Fiber (op U)) :
    Functor.toOpFiber p (Functor.fromOpFiber p x) = x := sorry

/-- A fibre morphism over `𝟙 U` opposes to a fibre morphism of `p.op` over `𝟙 (op U)`. -/
def Functor.toOpFiberHom (p : F ⥤ C) {U : C} {x y : p.Fiber U} (φ : x ⟶ y) :
    Functor.toOpFiber p y ⟶ Functor.toOpFiber p x :=
  ⟨φ.val.op, sorry⟩

/-- A fibre morphism of `p.op` unopposes to a fibre morphism of `p`. -/
def Functor.fromOpFiberHom (p : F ⥤ C) {U : C} {x y : p.op.Fiber (op U)} (φ : x ⟶ y) :
    Functor.fromOpFiber p y ⟶ Functor.fromOpFiber p x :=
  ⟨φ.val.unop, sorry⟩

/-- Pushforward of a fibre object along `f`, using a cleavage of `p.op`. -/
noncomputable def Functor.pushforwardFiberObj (p : F ⥤ C) (χ : p.op.Cleavage)
    {U V : C} (f : U ⟶ V) (x : p.Fiber U) : p.Fiber V :=
  Functor.fromOpFiber p ((χ.reindex f.op).obj (Functor.toOpFiber p x))

/-- The action on fibre morphisms induced by the chosen pushforwards along a base arrow. -/
noncomputable def Functor.pushforwardFiberMap (p : F ⥤ C) (χ : p.op.Cleavage)
    {U V : C} (f : U ⟶ V) {x y : p.Fiber U} (φ : x ⟶ y) :
    Functor.pushforwardFiberObj p χ f x ⟶ Functor.pushforwardFiberObj p χ f y :=
  Functor.fromOpFiberHom p ((χ.reindex f.op).map (Functor.toOpFiberHom p φ))

/-- The pushforward action on fibre morphisms preserves identity arrows. -/
theorem Functor.pushforwardFiberMap.id (p : F ⥤ C) (χ : p.op.Cleavage)
    {U V : C} (f : U ⟶ V) (x : p.Fiber U) :
    Functor.pushforwardFiberMap p χ f (𝟙 x) = 𝟙 (Functor.pushforwardFiberObj p χ f x) := sorry

/-- The pushforward action on fibre morphisms preserves composition. -/
theorem Functor.pushforwardFiberMap.comp (p : F ⥤ C) (χ : p.op.Cleavage)
    {U V : C} (f : U ⟶ V) {x y z : p.Fiber U} (φ : x ⟶ y) (ψ : y ⟶ z) :
    Functor.pushforwardFiberMap p χ f (φ ≫ ψ) =
      Functor.pushforwardFiberMap p χ f φ ≫ Functor.pushforwardFiberMap p χ f ψ := sorry

/-- The fibre functor of a chosen cleavage of `p.op`, covariant in the base. -/
noncomputable def Functor.pushforwardFiberFunctor (p : F ⥤ C) (χ : p.op.Cleavage)
    {U V : C} (f : U ⟶ V) : p.Fiber U ⥤ p.Fiber V where
  obj x := Functor.pushforwardFiberObj p χ f x
  map := Functor.pushforwardFiberMap p χ f
  map_id := Functor.pushforwardFiberMap.id p χ f
  map_comp := Functor.pushforwardFiberMap.comp p χ f

/-- The object action of `pushforwardFiberFunctor` is `pushforwardFiberObj`. -/
@[simp]
theorem Functor.pushforwardFiberFunctor.obj (p : F ⥤ C) (χ : p.op.Cleavage)
    {U V : C} (f : U ⟶ V) (x : p.Fiber U) :
    (Functor.pushforwardFiberFunctor p χ f).obj x =
      Functor.pushforwardFiberObj p χ f x := sorry

end CategoryTheory
