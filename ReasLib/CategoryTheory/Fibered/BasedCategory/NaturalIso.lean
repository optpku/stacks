module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.Fiber

/-!
# Based natural isomorphisms

This module supplies ordinary and fiberwise computations for natural isomorphisms between based
functors, including construction from vertical objectwise components.
-/

@[expose] public section

namespace CategoryTheory

open BasedCategory
open BasedFunctor
open BasedNatTrans
open Functor.IsHomLift
open scoped Bicategory

universe u v uS uX uY vS vX vY

variable {C : Type u} [Category.{v} C]

namespace BasedNatIso

variable {X : BasedCategory.{vX, uX} C} {Y : BasedCategory.{vY, uY} C}
variable {F G H : X ⥤ᵇ Y}

/-- Forget a based natural isomorphism to the corresponding natural isomorphism between
underlying total-category functors. This is the neutral data owner used by all more specialized
fibred-category forgetful APIs. -/
def toNatIso (e : F ≅ G) : F.toFunctor ≅ G.toFunctor :=
  (BasedNatTrans.forgetful X Y).mapIso e

/-- The forward transformation of `toNatIso e` is the underlying forward based natural
transformation. -/
@[simp]
theorem toNatIso.hom (e : F ≅ G) :
    (toNatIso e).hom = e.hom.toNatTrans := sorry

/-- The inverse transformation of `toNatIso e` is the underlying inverse based natural
transformation. -/
@[simp]
theorem toNatIso.inv (e : F ≅ G) :
    (toNatIso e).inv = e.inv.toNatTrans := sorry

/-- The forward component of `toNatIso e` is the corresponding total-category component. -/
@[simp]
theorem toNatIso.hom.app (e : F ≅ G) (x : X.obj) :
    (toNatIso e).hom.app x = e.hom.toNatTrans.app x := sorry

/-- The inverse component of `toNatIso e` is the corresponding total-category component. -/
@[simp]
theorem toNatIso.inv.app (e : F ≅ G) (x : X.obj) :
    (toNatIso e).inv.app x = e.inv.toNatTrans.app x := sorry

/-- Forgetting the identity based natural isomorphism gives the identity natural
isomorphism. -/
@[simp]
theorem toNatIso.refl (F : X ⥤ᵇ Y) :
    toNatIso (Iso.refl F) = Iso.refl F.toFunctor := sorry

/-- Forgetting a based natural isomorphism commutes with symmetry. -/
@[simp]
theorem toNatIso.symm (e : F ≅ G) :
    toNatIso e.symm = (toNatIso e).symm := sorry

/-- Forgetting based natural isomorphisms preserves composition. -/
theorem toNatIso.trans (e : F ≅ G) (d : G ≅ H) :
    toNatIso (e ≪≫ d) = toNatIso e ≪≫ toNatIso d := sorry

/-- Construct a based natural isomorphism from objectwise isomorphisms, forward naturality, and
verticality over the identity. Inverse naturality and inverse verticality are derived by the
canonical ordinary and based isomorphism constructors. -/
def ofComponents
    (e : ∀ x : X.obj, F.obj x ≅ G.obj x)
    (naturality : ∀ {x y : X.obj} (f : x ⟶ y),
      F.map f ≫ (e y).hom = (e x).hom ≫ G.map f)
    (isHomLift : ∀ x : X.obj,
      Y.p.IsHomLift (𝟙 (X.p.obj x)) (e x).hom) :
    F ≅ G :=
  BasedNatIso.mkNatIso
    (NatIso.ofComponents e naturality)
    isHomLift

/-- The forward component of a based natural isomorphism constructed by `ofComponents` is the
supplied forward component. -/
@[simp]
theorem ofComponents.hom.app
    (e : ∀ x : X.obj, F.obj x ≅ G.obj x)
    (naturality : ∀ {x y : X.obj} (f : x ⟶ y),
      F.map f ≫ (e y).hom = (e x).hom ≫ G.map f)
    (isHomLift : ∀ x : X.obj,
      Y.p.IsHomLift (𝟙 (X.p.obj x)) (e x).hom)
    (x : X.obj) :
    (ofComponents e naturality isHomLift).hom.toNatTrans.app x =
      (e x).hom := sorry

/-- The inverse component of a based natural isomorphism constructed by `ofComponents` is the
supplied inverse component. -/
@[simp]
theorem ofComponents.inv.app
    (e : ∀ x : X.obj, F.obj x ≅ G.obj x)
    (naturality : ∀ {x y : X.obj} (f : x ⟶ y),
      F.map f ≫ (e y).hom = (e x).hom ≫ G.map f)
    (isHomLift : ∀ x : X.obj,
      Y.p.IsHomLift (𝟙 (X.p.obj x)) (e x).hom)
    (x : X.obj) :
    (ofComponents e naturality isHomLift).inv.toNatTrans.app x =
      (e x).inv := sorry

/-- A based natural isomorphism restricts canonically to a natural isomorphism on every standard
fiber. -/
def fiber (e : F ≅ G) (U : C) : F.fiberFunctor U ≅ G.fiberFunctor U :=
  (BasedCategory.fiberFunctor X Y U).mapIso e

/-- The forward transformation of a restricted based natural isomorphism is the restriction of
its forward based natural transformation. -/
@[simp]
theorem fiber.hom (e : F ≅ G) (U : C) :
    (fiber e U).hom = BasedNatTrans.fiber e.hom U := sorry

/-- The inverse transformation of a restricted based natural isomorphism is the restriction of
its inverse based natural transformation. -/
@[simp]
theorem fiber.inv (e : F ≅ G) (U : C) :
    (fiber e U).inv = BasedNatTrans.fiber e.inv U := sorry

/-- The forward component of a restricted based natural isomorphism is the canonical bundled
fiber component. -/
@[simp]
theorem fiber.hom.app (e : F ≅ G) (U : C) (x : X.p.Fiber U) :
    (fiber e U).hom.app x = BasedNatTrans.fiberApp e.hom U x := sorry

/-- The inverse component of a restricted based natural isomorphism is the canonical bundled
fiber component. -/
@[simp]
theorem fiber.inv.app (e : F ≅ G) (U : C) (x : X.p.Fiber U) :
    (fiber e U).inv.app x = BasedNatTrans.fiberApp e.inv U x := sorry

/-- Forgetting the forward fiber component recovers the original total-category component. -/
@[simp]
theorem fiber.hom.app.val (e : F ≅ G) (U : C) (x : X.p.Fiber U) :
    ((fiber e U).hom.app x).1 = e.hom.toNatTrans.app x.1 := sorry

/-- Forgetting the inverse fiber component recovers the original total-category component. -/
@[simp]
theorem fiber.inv.app.val (e : F ≅ G) (U : C) (x : X.p.Fiber U) :
    ((fiber e U).inv.app x).1 = e.inv.toNatTrans.app x.1 := sorry

/-- Restricting the identity based natural isomorphism gives the identity fiber
isomorphism. -/
@[simp]
theorem fiber.refl (F : X ⥤ᵇ Y) (U : C) :
    fiber (Iso.refl F) U = Iso.refl (F.fiberFunctor U) := sorry

/-- Restriction to a fiber commutes with reversing a based natural isomorphism. -/
@[simp]
theorem fiber.symm (e : F ≅ G) (U : C) :
    fiber e.symm U = (fiber e U).symm := sorry

/-- Restriction to a fiber preserves composition of based natural isomorphisms. -/
theorem fiber.trans (e : F ≅ G) (d : G ≅ H) (U : C) :
    fiber (e ≪≫ d) U = fiber e U ≪≫ fiber d U := sorry

end BasedNatIso

end CategoryTheory
