/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GeometricPoint.FiniteEtale
public import stacks_project.Chap58.Lemma_58_5_5

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

universe u

/-- The finite étale geometric-fiber functor at a geometric point. -/
noncomputable abbrev standardFiniteEtaleFiber {X : Scheme.{u}} [ConnectedSpace X]
    (xbar : GeometricPoint X) : FiniteEtale X ⥤ FintypeCat.{u} :=
  GeometricPoint.finiteFiber xbar

/-- The geometric point obtained by postcomposing with a scheme morphism. -/
noncomputable abbrev geometricPointPostcomp {X Y : Scheme.{u}}
    (xbar : GeometricPoint X) (f : X ⟶ Y) : GeometricPoint Y :=
  GeometricPoint.map xbar f

/-- The underlying morphism of a postcomposed geometric point. -/
theorem geometricPointPostcomp_hom {X Y : Scheme.{u}}
    (xbar : GeometricPoint X) (f : X ⟶ Y) :
    (geometricPointPostcomp xbar f).hom = xbar.hom ≫ f :=
  GeometricPoint.map_hom xbar f

/-- The finite étale fiber comparison along a scheme morphism. -/
noncomputable abbrev standardFiniteEtaleFiber_baseChangeIso {X Y : Scheme.{u}}
    [ConnectedSpace X] [ConnectedSpace Y] (f : X ⟶ Y) (xbar : GeometricPoint X) :
    finiteEtaleBaseChange f ⋙ standardFiniteEtaleFiber xbar ≅
      standardFiniteEtaleFiber (geometricPointPostcomp xbar f) :=
  GeometricPoint.finiteFiberBaseChangeIso f xbar

/-- The finite continuous action functor associated with a geometric fiber. -/
noncomputable abbrev functorToContAction_finiteEtaleFiber {X : Scheme.{u}} [ConnectedSpace X]
    (xbar : GeometricPoint X) :=
  GeometricPoint.fiberAction xbar
