module

public import ReasLib.AlgebraicGeometry.Scheme.WeaklyAssociatedPoints
public import stacks_project.Chap66.Lemma_66_4_2_Comparison
public import stacks_project.Chap66.Lemma_66_16_4_Etale

/-!
# Weakly associated points of algebraic spaces

A point of an algebraic space is weakly associated when it is weakly associated
for the structure sheaf, witnessed on some étale scheme chart.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A point of an algebraic space is weakly associated when some étale morphism
from a scheme has a weakly associated point mapping to it. -/
def weaklyAssociatedAt {S : Scheme.{u}} (X : AlgebraicSpace S) (x : Points X) :
    Prop :=
  ∃ (U : Over S) (a : ofOver U ⟶ X) (u : U.left),
    Etale a ∧ Points.map a (ofOver.pointsEquiv U u) = x ∧ u ∈ U.left.weakAss

/-- The set of weakly associated points of an algebraic space. -/
def weakAss {S : Scheme.{u}} (X : AlgebraicSpace S) : Set (Points X) :=
  {x | weaklyAssociatedAt X x}

/-- Membership in `X.weakAss` is the étale-chart weakly-associated-point
predicate. -/
theorem mem_weakAss_iff {S : Scheme.{u}} (X : AlgebraicSpace S) (x : Points X) :
    x ∈ X.weakAss ↔ weaklyAssociatedAt X x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
