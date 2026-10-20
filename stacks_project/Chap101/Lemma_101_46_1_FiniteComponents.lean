module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.FiniteComponents
public import Mathlib.Topology.Irreducible
public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.FiniteComponents.Locality
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.Comparison
public import stacks_project.Chap67.Lemma_67_49_1_FiniteComponents
public import stacks_project.Chap100.Definition_100_6_1_QuasiCompact
public import stacks_project.Chap100.Definition_100_7_2_SmoothLocal
public import stacks_project.Chap100.Lemma_100_7_1_SmoothLocal
public import stacks_project.Chap101.Definition_101_13_2_Closed
public import stacks_project.Chap103.«103_15_1_1_Smooth»

/-!
# Finite irreducible components on compact opens of algebraic stacks

This typed compatibility bridge retains the historical imports used by normalization.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

#check (AlgebraicGeometry.AlgebraicStack.HasFiniteIrreducibleComponentsOnCompactOpens :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X], Prop)
