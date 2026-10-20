module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GermProperty
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.Scheme.GermProperty
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_4_2_Comparison
public import stacks_project.Chap66.Lemma_66_5_5_PointsTopology

/-!
# Étale-local germ transfer at a point of an algebraic space

An étale-local property of scheme germs may be tested on étale morphisms from schemes through a
fixed point of an algebraic space: the “for any chart” and “for some chart” conditions are the
basic predicates.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.existsEtaleAt :
  ∀ {S : Scheme.{u}} (P : GermProperty.{u}) (X : AlgebraicSpace S) (x : Points X), Prop)

#check (AlgebraicGeometry.AlgebraicSpace.forallEtaleAt :
  ∀ {S : Scheme.{u}} (P : GermProperty.{u}) (X : AlgebraicSpace S) (x : Points X), Prop)

end AlgebraicGeometry.AlgebraicSpace
