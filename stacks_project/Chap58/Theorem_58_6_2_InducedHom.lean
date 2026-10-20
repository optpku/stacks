/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.FundamentalGroup
public import stacks_project.Chap58.Theorem_58_6_2_Fiber

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped FintypeCatDiscrete

universe u

/-- The continuous fundamental-group homomorphism induced by finite étale base change. -/
noncomputable abbrev etaleFundamentalGroupMap {X Y : Scheme.{u}}
    [ConnectedSpace X] [ConnectedSpace Y]
    (f : X ⟶ Y) (xbar : GeometricPoint X) :
    ContinuousMonoidHom
      (Aut (standardFiniteEtaleFiber xbar))
      (Aut (standardFiniteEtaleFiber (geometricPointPostcomp xbar f))) :=
  GeometricPoint.fundamentalGroupMap f xbar

/-- Restriction of finite continuous actions along the induced fundamental-group homomorphism. -/
noncomputable abbrev etaleFundamentalGroupMap_res {X Y : Scheme.{u}}
    [ConnectedSpace X] [ConnectedSpace Y]
    (f : X ⟶ Y) (xbar : GeometricPoint X) :=
  GeometricPoint.fundamentalGroupRestriction f xbar

/-- The continuous homomorphism induced by an isomorphism of geometric-fiber functors. -/
noncomputable abbrev inducedAutHom_of_fiberIso {X : Scheme.{u}} [ConnectedSpace X]
    {xbar xbar' : GeometricPoint X}
    (t : standardFiniteEtaleFiber xbar ≅ standardFiniteEtaleFiber xbar') :
    ContinuousMonoidHom
      (Aut (standardFiniteEtaleFiber xbar))
      (Aut (standardFiniteEtaleFiber xbar')) :=
  GeometricPoint.autHom t
