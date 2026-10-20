/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Closed
public import stacks_project.Chap100.Lemma_100_4_3_Comparison
public import stacks_project.Chap94.Definition_94_12_1_MorphismProperty

/-!
# Closed morphisms of algebraic stacks

The closedness API uses the canonical point topology and all algebraic-stack
base changes. The historical comparison and morphism-property imports remain
available to users of this source bridge.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

#check (AlgebraicGeometry.AlgebraicStack.Points.mapOfSlice :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] {U : Over S},
    (GroupoidsOver.slice U ⟶ X) → U.left → AlgebraicGeometry.AlgebraicStack.Points X)

#check (AlgebraicGeometry.AlgebraicStack.Points.topology :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    TopologicalSpace (AlgebraicGeometry.AlgebraicStack.Points X))

#check (AlgebraicGeometry.AlgebraicStack.IsPointsTopology :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    TopologicalSpace (AlgebraicGeometry.AlgebraicStack.Points X) → Prop)

#check (AlgebraicGeometry.AlgebraicStack.Closed :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y],
    (X ⟶ Y) → Prop)

#check (AlgebraicGeometry.AlgebraicStack.UniversallyClosed :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y],
    (X ⟶ Y) → Prop)
