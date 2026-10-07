module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Types.Basic
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Fiber
public import ReasLib.CategoryTheory.Fibered.Cleavage.Basic.Reindex.Functor
public import ReasLib.CategoryTheory.Fibered.FiberIsoClassPresheaf.Basic
public import ReasLib.CategoryTheory.Functor.IsomorphismClasses
public import stacks_project.Chap90.Remarks_90_5_2_Groupoids
public import stacks_project.Chap90.Remarks_90_5_2_Pushforward

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

/-- The fibre functor of a chosen cleavage of `p.op`, covariant in the base. -/
noncomputable def Functor.pushforwardFiberFunctor (p : F ⥤ C) (χ : p.op.Cleavage)
    {U V : C} (f : U ⟶ V) : p.Fiber U ⥤ p.Fiber V where
  obj x := Functor.pushforwardFiberObj p χ f x
  map {x y} φ :=
    Functor.fromOpFiberHom p ((χ.reindex f.op).map (Functor.toOpFiberHom p φ))
  map_id := sorry
  map_comp := sorry

/-- The object action of `pushforwardFiberFunctor` is `pushforwardFiberObj`. -/
@[simp]
theorem Functor.pushforwardFiberFunctor.obj (p : F ⥤ C) (χ : p.op.Cleavage)
    {U V : C} (f : U ⟶ V) (x : p.Fiber U) :
    (Functor.pushforwardFiberFunctor p χ f).obj x =
      Functor.pushforwardFiberObj p χ f x := sorry

/-- The covariant functor of fibrewise isomorphism classes of a category cofibered in groupoids. -/
noncomputable def Functor.fiberIsoClassFunctor (p : F ⥤ C) [IsFibered.InGroupoids p.op] :
    C ⥤ Type uF where
  obj U := isomorphismClasses.obj (Cat.of (p.Fiber U))
  map {U V} f :=
    TypeCat.ofHom
      (Functor.pushforwardFiberFunctor p (Functor.cleavageOp p) f).isoClassesMap
  map_id := sorry
  map_comp := sorry

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

/-- Restriction of a represented fibrewise isomorphism class may be computed using any cleavage. -/
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
