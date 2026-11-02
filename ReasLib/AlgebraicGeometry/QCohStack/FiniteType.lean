/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.AlgebraicGeometry.QCohStack.Stack
public import ReasLib.CategoryTheory.Fibered.FullSubcategory.Stack
public import ReasLib.CategoryTheory.Fibered.Stack.Over.Projection
import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteType
import ReasLib.AlgebraicGeometry.QCohStack.StronglyCartesian
import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.LocalGeneration

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
  Iff.rfl

/-- Package a finite-type quasi-coherent pair as an object of the full subcategory. -/
def mk {S : Scheme.{u}} (x : Obj S) (h : x.sheaf.obj.IsFiniteType) :
    (objectProperty S).FullSubcategory where
  obj := x
  property := h

/-- The underlying `QCohStack` object of `mk x h` is `x`. -/
theorem mk_obj {S : Scheme.{u}} (x : Obj S) (h : x.sheaf.obj.IsFiniteType) :
    (mk x h).obj = x :=
  rfl

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
  rfl

/-- The morphism part of `p_fg` is the underlying morphism of `S`-schemes. -/
theorem p_map {S : Scheme.{u}} {x y : (objectProperty S).FullSubcategory}
    (f : x ⟶ y) : (p S).map f = f.hom.base :=
  rfl

/-- Finite type of quasi-coherent sheaves is stable under strongly cartesian
pullback in `QCohStack`. -/
theorem cartesianPullback (S : Scheme.{u}) :
    ObjectProperty.IsStableUnder.CartesianPullback (objectProperty S) (QCohStack.p S) := by
  intro R T f a b φ hφ hb
  haveI : (QCohStack.p S).IsStronglyCartesian ((QCohStack.p S).map φ) φ := by
    subst_hom_lift (QCohStack.p S) f φ
    exact hφ
  haveI : IsIso φ.sheaf :=
    (QCohStack.isStronglyCartesian_iff_isIso_sheaf φ).mp inferInstance
  haveI : b.sheaf.obj.IsFiniteType := hb
  haveI : ((Scheme.QCoh.pullback φ.base.left).obj b.sheaf).obj.IsFiniteType := by
    rw [Scheme.QCoh.pullback_obj]
    infer_instance
  have ha : a.sheaf.obj.IsFiniteType :=
    SheafOfModules.isFiniteType_of_iso
      (M := ((Scheme.QCoh.pullback φ.base.left).obj b.sheaf).obj)
      (N := a.sheaf.obj)
      ((Scheme.QCoh.inclusion a.base.left).mapIso (asIso φ.sheaf))
  exact ObjectProperty.le_isoClosure _ _ ha

/-- Finite type of quasi-coherent sheaves is fiberwise local for the fppf topology
on `(Sch/S)`. -/
theorem isFiberwiseLocal (S : Scheme.{u}) [(QCohStack.p S).IsFibered] :
    (objectProperty S).IsFiberwiseLocal (Scheme.fppfTopology.over S) (QCohStack.p S) :=
  sorry

/-- The projection from finite-type quasi-coherent sheaves over a scheme to its fppf site
is fibered, its fiber Hom-presheaves are sheaves, and its descent data are effective. -/
@[stacks 04U4, instance]
instance instIsStackOnSite (S : Scheme.{u}) :
    IsStack.OnSite (Scheme.fppfTopology.over S) (p S) :=
  ObjectProperty.FullSubcategory.isStackOnSite
    (Scheme.fppfTopology.over S) (QCohStack.p S) (objectProperty S)
    (cartesianPullback S) (isFiberwiseLocal S)

/-- The stack of finite-type quasi-coherent sheaves over `(Sch/S)_fppf`. -/
abbrev stack (S : Scheme.{u}) : StackOver (Scheme.fppfTopology.over S) :=
  StackOver.ofProjection (Scheme.fppfTopology.over S) (p S)

/-- The projection of `stack S` is the functor `p S`. -/
theorem stack_p (S : Scheme.{u}) : (stack S).p = p S :=
  rfl

end AlgebraicGeometry.QCohStack.FG
