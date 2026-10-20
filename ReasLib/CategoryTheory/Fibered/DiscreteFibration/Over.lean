module

public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.Slice
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fibers of slice projections

The fiber of `Over.forget X` over `U` has the arrows `U ⟶ X` as its objects. This file owns the
conversion independently of representable presheaves and exposes the computation rules needed by
discrete-fibration arguments.
-/

@[expose] public section

universe v u

namespace CategoryTheory.Over

variable {C : Type u} [Category.{v} C]

/-- Read an object of the fiber of `Over.forget X` as its underlying arrow to `X`. -/
@[stacks 0043 "slice-fiber object as an arrow"]
def fiberToHom {X U : C} (a : (Over.forget X).Fiber U) : U ⟶ X :=
  eqToHom a.2.symm ≫ a.1.hom

/-- Regard an arrow `f : U ⟶ X` as the corresponding object in the fiber of `Over.forget X`. -/
@[stacks 0043 "arrow as a slice-fiber object"]
def homToFiber {X U : C} (f : U ⟶ X) : (Over.forget X).Fiber U :=
  ⟨Over.mk f, rfl⟩

/-- The slice object underlying `homToFiber f` lies over the domain of `f`. -/
@[simp]
theorem homToFiber.obj_eq {X U : C} (f : U ⟶ X) :
    (Over.forget X).obj (Over.mk f) = U := sorry

/-- Reading the fiber object built from an arrow recovers that arrow. -/
@[simp]
theorem fiberToHom.homToFiber {X U : C} (f : U ⟶ X) :
    fiberToHom (homToFiber f) = f := sorry

/-- Rebuilding a slice-fiber object from its underlying arrow recovers the original object. -/
@[simp]
theorem homToFiber.fiberToHom {X U : C} (a : (Over.forget X).Fiber U) :
    homToFiber (fiberToHom a) = a := sorry

/-- Objects in the fiber of `Over.forget X` over `U` are canonically the arrows `U ⟶ X`. -/
@[stacks 0043 "slice-fiber objects as arrows"]
def fiberObjEquiv (X U : C) : (Over.forget X).Fiber U ≃ (U ⟶ X) where
  toFun := fiberToHom
  invFun := homToFiber
  left_inv := homToFiber.fiberToHom
  right_inv := fiberToHom.homToFiber

/-- A morphism inside one slice fiber preserves the corresponding arrow to `X`. -/
theorem fiberToHom.eq_of_hom
    {X U : C} {a b : (Over.forget X).Fiber U} (φ : a ⟶ b) :
    fiberToHom a = fiberToHom b := sorry

/-- A lift over `f : Y ⟶ Z` in a slice projection records precomposition by `f` on the
corresponding arrows to `X`. -/
theorem fiberToHom.eq_comp_of_isHomLift
    {X Y Z : C} {a : (Over.forget X).Fiber Y}
    {b : (Over.forget X).Fiber Z} {f : Y ⟶ Z} {h : a.1 ⟶ b.1}
    [Functor.IsHomLift (Over.forget X) f h] :
    fiberToHom a = f ≫ fiberToHom b := sorry

/-- Explicit-proof bridge for the slice-fiber computation of a hom lift. -/
theorem fiberToHom.eq_comp_of_isHomLift.explicit
    {X Y Z : C} {a : (Over.forget X).Fiber Y}
    {b : (Over.forget X).Fiber Z} {f : Y ⟶ Z} {h : a.1 ⟶ b.1}
    (hh : Functor.IsHomLift (Over.forget X) f h) :
    fiberToHom a = f ≫ fiberToHom b := sorry

end CategoryTheory.Over
