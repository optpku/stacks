/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cohomology
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Grothendieck
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Monoidal
public import ReasLib.CategoryTheory.Monoidal.Closed.Exactness
public import ReasLib.Topology.Sheaves.Abelian.Sheafification

/-!
# Ext of module sheaves on ringed spaces

Sheaf Ext is right-derived internal Hom. Global Ext from the structure module is identified
with cohomology of the underlying additive sheaf.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalClosed AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Ext

/-- Sheaf Ext of module sheaves is the right-derived internal Hom. -/
abbrev sheafExt {X : RingedSpace.{u}} (F G : X.Modules) (i : ℕ) : X.Modules :=
  ((ihom F).rightDerived i).obj G

/-- Sheaf Ext is the value of the right-derived internal Hom from its first argument on its
second argument. -/
theorem sheafExt_def {X : RingedSpace.{u}} (F G : X.Modules) (i : ℕ) :
    sheafExt F G i = ((ihom F).rightDerived i).obj G := sorry

/-- Degree-zero sheaf Ext is isomorphic to internal Hom. -/
theorem sheafExt_zero {X : RingedSpace.{u}} (F G : X.Modules) :
    IsIsomorphic (sheafExt F G 0) ((ihom F).obj G) := sorry

/-- Global Ext from the structure module is isomorphic to sheaf cohomology. -/
theorem ext_unit_cohomology {X : RingedSpace.{u}} (G : X.Modules) (i : ℕ) :
    IsIsomorphic (AddCommGrpCat.of (Abelian.Ext (SheafOfModules.unit X.ringCatSheaf) G i))
      (AlgebraicGeometry.RingedSpace.moduleCohomology G i) := sorry

end AlgebraicGeometry.RingedSpace.Ext
