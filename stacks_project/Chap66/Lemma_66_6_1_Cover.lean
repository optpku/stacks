module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AffineEtaleCover
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap66.Definition_66_4_1_Points

/-!
# Affine étale covers of algebraic spaces

The affine étale cover API is owned by the reusable mathematical library. This module
preserves the chapter-facing import surface and checks the complete existence statement.
-/

@[expose] public section

universe u

#check (AlgebraicGeometry.AlgebraicSpace.exists_affineEtaleCover :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S),
    Nonempty (AlgebraicGeometry.AlgebraicSpace.AffineEtaleCover.{u, u} X))
