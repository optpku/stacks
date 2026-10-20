module

public import ReasLib.CategoryTheory.DisplayedCategory.Fiber.Functor
public import ReasLib.CategoryTheory.DisplayedCategory.NatTrans

/-!
# Displayed natural transformations on intrinsic fibers

A displayed natural transformation over the identity transformation of any base functor restricts
to an ordinary natural transformation on every intrinsic fiber.
-/

@[expose] public section

namespace CategoryTheory

universe v u v' u'

variable {C : Type u} [Category.{v} C]
variable {C' : Type u'} [Category.{v'} C']
variable {D : DisplayedCategory C} {E : DisplayedCategory C'}
variable {F : C ⥤ C'}
variable {Phi Psi Chi : DisplayedFunctor D E F}

namespace DisplayedNatTrans

/-- The component of an identity-base displayed transformation in an intrinsic fiber. -/
def fiberApp (eta : DisplayedNatTrans Phi Psi (𝟙 F)) (X : C)
    (x : DisplayedCategory.Fiber D X) :
    E.Hom (𝟙 (F.obj X)) (Phi.obj x) (Psi.obj x) :=
  DisplayedCategory.Hom.cast E (by simp) (eta.app x)

namespace fiberApp

/-- Naturality of the component of an identity-base displayed transformation in an intrinsic
fiber. -/
@[reassoc]
theorem naturality
    (eta : DisplayedNatTrans Phi Psi (𝟙 F)) (X : C)
    {x y : DisplayedCategory.Fiber D X} (f : x ⟶ y) :
    (DisplayedFunctor.fiberFunctor Phi X).map f ≫ fiberApp eta X y =
      fiberApp eta X x ≫ (DisplayedFunctor.fiberFunctor Psi X).map f := sorry

end fiberApp

/-- The natural transformation on an intrinsic fiber induced by an identity-base displayed
natural transformation. -/
def fiber (eta : DisplayedNatTrans Phi Psi (𝟙 F)) (X : C) :
    DisplayedFunctor.fiberFunctor Phi X ⟶ DisplayedFunctor.fiberFunctor Psi X where
  app x := fiberApp eta X x
  naturality := fun {x y} f => fiberApp.naturality eta X (x := x) (y := y) f

/-- Components of the fiber restriction are the original displayed components. -/
@[simp]
theorem fiber_app (eta : DisplayedNatTrans Phi Psi (𝟙 F)) (X : C)
    (x : DisplayedCategory.Fiber D X) :
    (fiber eta X).app x = fiberApp eta X x := sorry

/-- Restriction of the identity displayed transformation is the identity fiber transformation. -/
@[simp]
theorem fiber_id (Phi : DisplayedFunctor D E F) (X : C) :
    fiber (DisplayedNatTrans.id Phi) X = 𝟙 (DisplayedFunctor.fiberFunctor Phi X) := sorry

/-- Restriction to a fiber preserves vertical composition of displayed transformations. -/
@[simp]
theorem fiber_comp
    (eta : DisplayedNatTrans Phi Psi (𝟙 F))
    (theta : DisplayedNatTrans Psi Chi (𝟙 F)) (X : C) :
    fiber (DisplayedNatTrans.vcomp eta theta) X =
      fiber eta X ≫ fiber theta X := sorry

end DisplayedNatTrans

end CategoryTheory
