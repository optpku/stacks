/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.CategoryTheory.Fibered.FullSubcategory.Stack
public import stacks_project.Chap95.«95_4_0_1_Category»

/-!
# Finite-type quasi-coherent objects over a base scheme

The full subcategory of `QCohStack` on pairs `(T, F)` with `F` of finite type,
together with the restricted projection `p_fg`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.QCohStack.FG

/-- Objects `(T, F)` of `QCohStack` whose quasi-coherent sheaf is of finite type. -/
def objectProperty (S : Scheme.{u}) : ObjectProperty (Obj S) :=
  fun x ↦ x.sheaf.obj.IsFiniteType

/-- Membership in the finite-type cut is finite type of the underlying module sheaf. -/
theorem objectProperty_iff (S : Scheme.{u}) (x : Obj S) :
    objectProperty S x ↔ x.sheaf.obj.IsFiniteType :=
  sorry

/-- Package a finite-type quasi-coherent pair as an object of the full subcategory. -/
def mk {S : Scheme.{u}} (x : Obj S) (h : x.sheaf.obj.IsFiniteType) :
    (objectProperty S).FullSubcategory where
  obj := x
  property := h

/-- The underlying `QCohStack` object of `mk x h` is `x`. -/
theorem mk_obj {S : Scheme.{u}} (x : Obj S) (h : x.sheaf.obj.IsFiniteType) :
    (mk x h).obj = x :=
  sorry

/-- A finite-type object of `QCohStack` has an underlying finite-type module sheaf. -/
instance instIsFiniteType_sheaf {S : Scheme.{u}}
    (x : (objectProperty S).FullSubcategory) :
    x.obj.sheaf.obj.IsFiniteType :=
  x.property

/-- The functor `p_fg` is the restriction of `QCohStack.p` to the finite-type full
subcategory. -/
def p (S : Scheme.{u}) : (objectProperty S).FullSubcategory ⥤ Over S :=
  (objectProperty S).ι ⋙ QCohStack.p S

/-- The object part of `p_fg` is the underlying `S`-scheme. -/
theorem p_obj {S : Scheme.{u}} (x : (objectProperty S).FullSubcategory) :
    (p S).obj x = x.obj.base :=
  sorry

/-- The morphism part of `p_fg` is the underlying morphism of `S`-schemes. -/
theorem p_map {S : Scheme.{u}} {x y : (objectProperty S).FullSubcategory}
    (f : x ⟶ y) : (p S).map f = f.hom.base :=
  sorry

/-- Finite type of quasi-coherent sheaves is stable under strongly cartesian
pullback in `QCohStack`. -/
theorem cartesianPullback (S : Scheme.{u}) :
    ObjectProperty.IsStableUnder.CartesianPullback (objectProperty S) (QCohStack.p S) :=
  sorry

/-- Finite type of quasi-coherent sheaves is fiberwise local for the fppf topology
on `(Sch/S)`. -/
theorem isFiberwiseLocal (S : Scheme.{u}) [(QCohStack.p S).IsFibered] :
    (objectProperty S).IsFiberwiseLocal (Scheme.fppfTopology.over S) (QCohStack.p S) :=
  sorry

end AlgebraicGeometry.QCohStack.FG
