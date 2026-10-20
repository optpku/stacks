module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleNeighborhood
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.AlgebraicGeometry.Scheme.FieldValuedPoint
public import stacks_project.Chap66.Definition_66_18_1_Site
public import stacks_project.Chap66.Lemma_66_4_2_Comparison
public import stacks_project.Chap66.Lemma_66_5_5_PointsTopology

/-!
# Étale neighbourhoods of algebraic-space points

The canonical definitions and their API are owned by `ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleNeighborhood`.
This chapter module preserves the original import surface.
-/

universe u

#check (AlgebraicGeometry.AlgebraicSpace.EtaleNeighborhood :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S)
    (x : AlgebraicGeometry.AlgebraicSpace.Points X), Type (u + 1))
