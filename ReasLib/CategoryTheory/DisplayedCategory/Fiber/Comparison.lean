module

public import ReasLib.CategoryTheory.DisplayedCategory.Fiber
public import Mathlib.CategoryTheory.FiberedCategory.HasFibers

/-!
# Comparison of displayed and strict fibers

This leaf connects the intrinsic displayed fiber with Mathlib's strict `Functor.Fiber`.  The
intrinsic category itself remains available from `DisplayedCategory.Fiber` without importing this
comparison layer.
-/

@[expose] public section

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

namespace DisplayedCategory.Fiber

/-- The canonical functor from the intrinsic displayed fiber to Mathlib's strict fiber. -/
def toFunctorFiber (D : DisplayedCategory C) (X : C) :
    Fiber D X ⥤ Functor.Fiber (DisplayedCategory.Total.forget D) X :=
  Functor.Fiber.inducedFunctor (inclusion_comp_forget D X)

namespace toFunctorFiber

/-- The underlying total object of a `toFunctorFiber` image. -/
@[simp]
theorem obj_val (D : DisplayedCategory C) (X : C) (x : Fiber D X) :
    ((toFunctorFiber D X).obj x).1 =
      (⟨X, x⟩ : DisplayedCategory.Total D) := sorry

/-- The base equality carried by a `toFunctorFiber` object is canonical. -/
@[simp]
theorem obj_base (D : DisplayedCategory C) (X : C) (x : Fiber D X) :
    (DisplayedCategory.Total.forget D).obj ((toFunctorFiber D X).obj x).1 = X := sorry

/-- The underlying total morphism of a `toFunctorFiber` image. -/
@[simp]
theorem map_val {D : DisplayedCategory C} (X : C)
    {x y : Fiber D X} (f : x ⟶ y) :
    ((toFunctorFiber D X).map f).1 =
      (inclusion D X).map f := sorry

end toFunctorFiber

/-- The canonical displayed-fiber comparison is an equivalence. -/
theorem isEquivalence (D : DisplayedCategory C) (X : C) :
    (toFunctorFiber D X).IsEquivalence := sorry

attribute [instance] isEquivalence

/-- The explicit categorical equivalence between the intrinsic displayed fiber and Mathlib's
strict fiber of the total-category projection. -/
noncomputable def equivalence (D : DisplayedCategory C) (X : C) :
    Fiber D X ≌ Functor.Fiber (DisplayedCategory.Total.forget D) X :=
  (toFunctorFiber D X).asEquivalence

/-- The functor of `equivalence` is the canonical displayed-fiber comparison. -/
@[simp]
theorem equivalence_functor (D : DisplayedCategory C) (X : C) :
    (equivalence D X).functor = toFunctorFiber D X := sorry

/-- The intrinsic displayed fibers form the canonical `HasFibers` structure on the total-category
projection. -/
instance hasFibers (D : DisplayedCategory C) :
    HasFibers (DisplayedCategory.Total.forget D) where
  Fib X := Fiber D X
  category X := category D X
  ι X := inclusion D X
  comp_const X := inclusion_comp_forget D X
  equiv X := isEquivalence D X

end DisplayedCategory.Fiber

end CategoryTheory
