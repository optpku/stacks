/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.FiberedCategory.Cocartesian
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.CategoryTheory.Fibered.Cleavage.Basic.Reindex.Lift
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic

/-!
# Covariant fibrewise isomorphism classes

The covariant functor of isomorphism classes of the fibres of a cofibered category.
-/

@[expose] public section

open CategoryTheory
open Opposite

universe u v uF vF

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C]
variable {F : Type uF} [Category.{vF} F]

namespace fiberIsoClassCopresheaf

/-- The opposite fibre object associated to a standard fibre object. -/
def toOpFiber (p : F ⥤ C) {U : C} (x : p.Fiber U) : p.op.Fiber (op U) :=
  ⟨op x.1, congrArg op x.2⟩

/-- The standard fibre object associated to an opposite fibre object. -/
def fromOpFiber (p : F ⥤ C) {U : C} (x : p.op.Fiber (op U)) : p.Fiber U :=
  ⟨unop x.1, congrArg unop x.2⟩

/-- The chosen pushforward of a fibre object along a base morphism. -/
noncomputable def pushforwardObj (p : F ⥤ C) [Functor.IsFibered.InGroupoids p.op]
    {U V : C} (f : U ⟶ V) (x : p.Fiber U) : p.Fiber V :=
  fromOpFiber p ((Cleavage.ofIsFibered p.op).reindexObj f.op (toOpFiber p x))

/-- The chosen strongly co-Cartesian pushforward morphism. -/
noncomputable def pushforwardHom (p : F ⥤ C) [Functor.IsFibered.InGroupoids p.op]
    {U V : C} (f : U ⟶ V) (x : p.Fiber U) : x.1 ⟶ (pushforwardObj p f x).1 :=
  ((Cleavage.ofIsFibered p.op).cartesianHom f.op (toOpFiber p x)).unop

/-- The chosen pushforward morphism is strongly co-Cartesian. -/
theorem pushforwardHom_isStronglyCocartesian (p : F ⥤ C)
    [Functor.IsFibered.InGroupoids p.op] {U V : C} (f : U ⟶ V) (x : p.Fiber U) :
    p.IsStronglyCocartesian f (pushforwardHom p f x) := sorry

/-- Chosen pushforwards carry isomorphic fibre objects to isomorphic fibre objects. -/
theorem pushforwardObj_respectsIso (p : F ⥤ C) [Functor.IsFibered.InGroupoids p.op]
    {U V : C} (f : U ⟶ V) {x y : p.Fiber U} (hxy : Nonempty (x ≅ y)) :
    Nonempty (pushforwardObj p f x ≅ pushforwardObj p f y) := sorry

/-- The raw quotient map induced by chosen pushforward of fibre objects. -/
noncomputable def rawMap (p : F ⥤ C) [Functor.IsFibered.InGroupoids p.op]
    {U V : C} (f : U ⟶ V) :
    isomorphismClasses.obj (Cat.of (p.Fiber U)) →
      isomorphismClasses.obj (Cat.of (p.Fiber V)) :=
  Quotient.map (pushforwardObj p f) (fun _ _ hxy => pushforwardObj_respectsIso p f hxy)

/-- The raw quotient map of an identity arrow is the identity on fibrewise isomorphism classes. -/
theorem map_id (p : F ⥤ C) [Functor.IsFibered.InGroupoids p.op] (U : C) :
    TypeCat.ofHom (rawMap p (𝟙 U)) =
      𝟙 (isomorphismClasses.obj (Cat.of (p.Fiber U))) := sorry

/-- The raw quotient map of a composite is the composite of the raw quotient maps. -/
theorem map_comp (p : F ⥤ C) [Functor.IsFibered.InGroupoids p.op]
    {U V W : C} (f : U ⟶ V) (g : V ⟶ W) :
    TypeCat.ofHom (rawMap p (f ≫ g)) =
      TypeCat.ofHom (rawMap p f) ≫ TypeCat.ofHom (rawMap p g) := sorry

end fiberIsoClassCopresheaf

/-- The covariant functor of fibrewise isomorphism classes. -/
noncomputable def fiberIsoClassCopresheaf (p : F ⥤ C) [Functor.IsFibered.InGroupoids p.op] :
    C ⥤ Type uF where
  obj U := isomorphismClasses.obj (Cat.of (p.Fiber U))
  map f := TypeCat.ofHom (fiberIsoClassCopresheaf.rawMap p f)
  map_id := fiberIsoClassCopresheaf.map_id p
  map_comp := fiberIsoClassCopresheaf.map_comp p

namespace fiberIsoClassCopresheaf

/-- The value of the covariant fibre-class functor at a base object. -/
theorem obj (p : F ⥤ C) [Functor.IsFibered.InGroupoids p.op] (U : C) :
    (fiberIsoClassCopresheaf p).obj U = isomorphismClasses.obj (Cat.of (p.Fiber U)) := rfl

/-- The covariant fibre-class functor sends a represented class to the represented pushforward. -/
theorem map_mk (p : F ⥤ C) [Functor.IsFibered.InGroupoids p.op] {U V : C}
    (f : U ⟶ V) (x : p.Fiber U) :
    (fiberIsoClassCopresheaf p).map f (Quotient.mk'' x) =
      Quotient.mk'' (pushforwardObj p f x) := sorry

/-- A morphism lifting a base arrow maps a represented class to the class of its codomain. -/
theorem map_eq_of_isHomLift (p : F ⥤ C) [Functor.IsFibered.InGroupoids p.op]
    {U V : C} (f : U ⟶ V) {x : p.Fiber U} {y : p.Fiber V} (φ : x.1 ⟶ y.1)
    [p.IsHomLift f φ] :
    (fiberIsoClassCopresheaf p).map f (Quotient.mk'' x) = Quotient.mk'' y := sorry

end fiberIsoClassCopresheaf
end CategoryTheory.Functor
