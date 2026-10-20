/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.CoveringLift
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation

/-!
# Fppf covering lifts for morphisms of algebraic stacks

A surjective, flat, locally finitely presented morphism of algebraic stacks
admits fppf-local lifts of every target object, up to isomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A surjective, flat, locally finitely presented morphism of algebraic stacks
admits an fppf covering of every scheme over which a target object is defined,
together with source objects whose images are isomorphic to the restrictions
of that target object. -/
@[stacks 06QA]
theorem exists_fppfCovering_iso {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [Surjective f] [Flat f] [LocallyOfFinitePresentation f]
    {U : Over S} (y : GroupoidsOver.slice U ⟶ Y) :
    Groupoids.Hom.existsCoveringLift StandardTopology.fppf f y :=
  sorry

end AlgebraicGeometry.AlgebraicStack
