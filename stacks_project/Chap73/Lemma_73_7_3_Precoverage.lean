module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fppf
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Sites.Precoverage
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat

/-!
# Fppf precoverage on algebraic spaces

The fppf precoverage of algebraic spaces over a scheme has flat, locally finitely
presented, jointly surjective covering families.
-/

@[expose] public section

universe u

#check (AlgebraicGeometry.AlgebraicSpace.fppfPrecoverage :
  ∀ S : AlgebraicGeometry.Scheme.{u},
    CategoryTheory.Precoverage (AlgebraicGeometry.AlgebraicSpace S))
