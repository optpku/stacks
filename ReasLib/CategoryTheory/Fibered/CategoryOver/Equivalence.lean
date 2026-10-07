module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.Pseudofunctor
public import ReasLib.CategoryTheory.Fibered.CategoryOver.Fiber
import Mathlib.Tactic.CrossRefAttribute

/-!
# Isomorphism API for fibred categories over a base

This module gives the local isomorphism action of the canonical inclusion into
`BasedCategory`, its total-category and fiberwise readouts, and the inverse
constructor from based-functor isomorphisms.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe u v w vS

namespace CategoryTheory

open BasedFunctor
open Bicategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver

variable {X Y : FiberedCategoryOver C}

/-- Forget an isomorphism of morphisms of fibred categories to the corresponding isomorphism of
underlying based functors. This is the canonical local action of `toBased`, not a separately
chosen comparison. -/
@[stacks 04Z4 "underlying based-functor isomorphism"]
def toBasedFunctorIso {F G : X ⟶ Y} (e : F ≅ G) :
    toBasedFunctor F ≅ toBasedFunctor G :=
  ((toBased C).mapFunctor X Y).mapIso e

/-- The forward component of `toBasedFunctorIso` is the underlying based natural
transformation of the forward owner `2`-cell. -/
@[simp]
theorem toBasedFunctorIso.hom {F G : X ⟶ Y} (e : F ≅ G) :
    (toBasedFunctorIso e).hom = e.hom.hom := sorry

/-- The inverse component of `toBasedFunctorIso` is the underlying based natural
transformation of the inverse owner `2`-cell. -/
@[simp]
theorem toBasedFunctorIso.inv {F G : X ⟶ Y} (e : F ≅ G) :
    (toBasedFunctorIso e).inv = e.inv.hom := sorry

/-- Forget an isomorphism of morphisms of fibred categories to the corresponding natural
isomorphism between their total-category functors. -/
@[stacks 04Z4 "underlying total-functor isomorphism"]
def toFunctorIso {F G : X ⟶ Y} (e : F ≅ G) :
    toFunctor F ≅ toFunctor G :=
  Pseudofunctor.mapToFunctorIso (toBased C).toPseudofunctor e

/-- The forward transformation of `toFunctorIso` is the underlying natural transformation of
the forward owner `2`-cell. -/
@[simp]
theorem toFunctorIso.hom {F G : X ⟶ Y} (e : F ≅ G) :
    (toFunctorIso e).hom = e.hom.hom.toNatTrans := sorry

/-- The inverse transformation of `toFunctorIso` is the underlying natural transformation of
the inverse owner `2`-cell. -/
@[simp]
theorem toFunctorIso.inv {F G : X ⟶ Y} (e : F ≅ G) :
    (toFunctorIso e).inv = e.inv.hom.toNatTrans := sorry

/-- The forward component of `toFunctorIso` is the total-category component of the forward
owner `2`-cell. -/
@[simp]
theorem toFunctorIso.hom.app {F G : X ⟶ Y} (e : F ≅ G) (x : X.total) :
    (toFunctorIso e).hom.app x = e.hom.hom.toNatTrans.app x := sorry

/-- The inverse component of `toFunctorIso` is the total-category component of the inverse
owner `2`-cell. -/
@[simp]
theorem toFunctorIso.inv.app {F G : X ⟶ Y} (e : F ≅ G) (x : X.total) :
    (toFunctorIso e).inv.app x = e.inv.hom.toNatTrans.app x := sorry

/-- Forgetting the identity owner isomorphism gives the identity total-functor isomorphism. -/
@[simp]
theorem toFunctorIso.refl (F : X ⟶ Y) :
    toFunctorIso (Iso.refl F) = Iso.refl (toFunctor F) := sorry

/-- Forgetting owner isomorphisms to total functors commutes with symmetry. -/
@[simp]
theorem toFunctorIso.symm {F G : X ⟶ Y} (e : F ≅ G) :
    toFunctorIso e.symm = (toFunctorIso e).symm := sorry

/-- Forgetting owner isomorphisms to total functors preserves composition. -/
theorem toFunctorIso.trans {F G H : X ⟶ Y} (e : F ≅ G) (d : G ≅ H) :
    toFunctorIso (e ≪≫ d) = toFunctorIso e ≪≫ toFunctorIso d := sorry

/-- An isomorphism of morphisms of fibred categories restricts canonically to a natural
isomorphism on every standard fiber. -/
@[stacks 04Z4 "fiberwise restriction of a fibred-functor isomorphism"]
def fiberFunctorIso {F G : X ⟶ Y} (e : F ≅ G) (U : C) :
    fiberFunctor F U ≅ fiberFunctor G U :=
  (fiberHomFunctor X Y U).mapIso e

/-- The forward transformation of a restricted owner isomorphism is the restricted forward
owner `2`-morphism. -/
@[simp]
theorem fiberFunctorIso.hom {F G : X ⟶ Y} (e : F ≅ G) (U : C) :
    (fiberFunctorIso e U).hom = fiberNatTrans e.hom U := sorry

/-- The inverse transformation of a restricted owner isomorphism is the restricted inverse
owner `2`-morphism. -/
@[simp]
theorem fiberFunctorIso.inv {F G : X ⟶ Y} (e : F ≅ G) (U : C) :
    (fiberFunctorIso e U).inv = fiberNatTrans e.inv U := sorry

/-- The identity owner isomorphism restricts to the identity natural isomorphism on every
standard fiber. -/
@[simp]
theorem fiberFunctorIso.refl (F : X ⟶ Y) (U : C) :
    fiberFunctorIso (Iso.refl F) U =
      Iso.refl (fiberFunctor F U) := sorry

/-- Restriction of owner isomorphisms to a fiber commutes with symmetry. -/
@[simp]
theorem fiberFunctorIso.symm {F G : X ⟶ Y} (e : F ≅ G) (U : C) :
    fiberFunctorIso e.symm U = (fiberFunctorIso e U).symm := sorry

/-- Restriction of owner isomorphisms to a fiber preserves composition. -/
theorem fiberFunctorIso.trans
    {F G H : X ⟶ Y} (e : F ≅ G) (d : G ≅ H) (U : C) :
    fiberFunctorIso (e ≪≫ d) U =
      fiberFunctorIso e U ≪≫ fiberFunctorIso d U := sorry

/-- The forward fiber component of an owner isomorphism is represented by the original
total-category component. -/
@[simp]
theorem fiberFunctorIso.hom.app.val {F G : X ⟶ Y} (e : F ≅ G)
    (U : C) (x : X.p.Fiber U) :
    ((fiberFunctorIso e U).hom.app x).1 =
      e.hom.hom.toNatTrans.app x.1 := sorry

/-- The inverse fiber component of an owner isomorphism is represented by the original
total-category component. -/
@[simp]
theorem fiberFunctorIso.inv.app.val {F G : X ⟶ Y} (e : F ≅ G)
    (U : C) (x : X.p.Fiber U) :
    ((fiberFunctorIso e U).inv.app x).1 =
      e.inv.hom.toNatTrans.app x.1 := sorry

/-- Naturality of the forward component of an owner isomorphism after restriction to a
fiber. -/
@[reassoc]
theorem fiberFunctorIso.hom.naturality {F G : X ⟶ Y} (e : F ≅ G)
    (U : C) {x y : X.p.Fiber U} (φ : x ⟶ y) :
    (fiberFunctor F U).map φ ≫ (fiberFunctorIso e U).hom.app y =
      (fiberFunctorIso e U).hom.app x ≫ (fiberFunctor G U).map φ := sorry

/-- Naturality of the inverse component of an owner isomorphism after restriction to a
fiber. -/
@[reassoc]
theorem fiberFunctorIso.inv.naturality {F G : X ⟶ Y} (e : F ≅ G)
    (U : C) {x y : X.p.Fiber U} (φ : x ⟶ y) :
    (fiberFunctor G U).map φ ≫ (fiberFunctorIso e U).inv.app y =
      (fiberFunctorIso e U).inv.app x ≫ (fiberFunctor F U).map φ := sorry

/-- Transport formula for the forward fiber component of an owner isomorphism along an
isomorphism in the source fiber. -/
theorem fiberFunctorIso.hom.app.transport {F G : X ⟶ Y} (e : F ≅ G)
    (U : C) {x y : X.p.Fiber U} (c : x ≅ y) :
    (fiberFunctorIso e U).hom.app y =
      (fiberFunctor F U).map c.inv ≫
        (fiberFunctorIso e U).hom.app x ≫
        (fiberFunctor G U).map c.hom := sorry

/-- Transport formula for the inverse fiber component of an owner isomorphism along an
isomorphism in the source fiber. -/
theorem fiberFunctorIso.inv.app.transport {F G : X ⟶ Y} (e : F ≅ G)
    (U : C) {x y : X.p.Fiber U} (c : x ≅ y) :
    (fiberFunctorIso e U).inv.app y =
      (fiberFunctor G U).map c.inv ≫
        (fiberFunctorIso e U).inv.app x ≫
        (fiberFunctor F U).map c.hom := sorry

/-- Lift an isomorphism of the underlying based functors to an isomorphism of morphisms of fibred
categories. The cartesian-preservation witnesses and the unrestricted `2`-morphism membership are
proof-only fields, so no additional mathematical data are chosen. -/
@[stacks 04Z4 "lift a based-functor isomorphism"]
def BasedFunctorIso.lift {F G : X ⟶ Y}
    (e : toBasedFunctor F ≅ toBasedFunctor G) : F ≅ G :=
  ObjectProperty.isoMk _ e

/-- The forward cell of a lifted based-functor isomorphism is the supplied forward cell. -/
@[simp]
theorem BasedFunctorIso.lift.hom {F G : X ⟶ Y}
    (e : toBasedFunctor F ≅ toBasedFunctor G) :
    (BasedFunctorIso.lift e).hom.hom = e.hom := sorry

/-- The inverse cell of a lifted based-functor isomorphism is the supplied inverse cell. -/
@[simp]
theorem BasedFunctorIso.lift.inv {F G : X ⟶ Y}
    (e : toBasedFunctor F ≅ toBasedFunctor G) :
    (BasedFunctorIso.lift e).inv.hom = e.inv := sorry

end FiberedCategoryOver

end CategoryTheory
