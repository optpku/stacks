module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RegularAt
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_4_2_Comparison
public import stacks_project.Chap66.Lemma_66_5_5_PointsTopology

/-!
# Regularity of an algebraic space at a point

An algebraic space is regular at a point when the local ring of every étale scheme chart
through that point is a regular local ring. Equivalently, this holds for some such chart.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

#check (AlgebraicGeometry.AlgebraicSpace.RegularAt :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S),
    AlgebraicGeometry.AlgebraicSpace.Points X → Prop)
