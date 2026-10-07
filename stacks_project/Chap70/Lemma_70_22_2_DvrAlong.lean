module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import stacks_project.Chap67.Lemma_67_42_5_Along
public import stacks_project.Chap69.Lemma_69_19_1_DVR

/-!
# DVR valuative uniqueness along a morphism of algebraic spaces

A morphism of algebraic spaces satisfies the uniqueness part of the DVR
valuative criterion along a second morphism when every valuative square whose
generic arrow factors through that morphism, and whose ring is a discrete
valuation ring, has at most one dotted lift.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace ValuativeCriterion.DVR.Along

/-- Every valuative square whose generic arrow factors through `h` and whose ring
is a discrete valuation ring has at most one dotted lift `Spec(A) ⟶ X`. -/
def Uniqueness {S : Scheme.{u}} {U X Y : AlgebraicSpace S} (h : U ⟶ X)
    (f : X ⟶ Y) : Prop :=
  ∀ sq : ValuativeCommSqFactorsThrough h f,
    IsDiscreteValuationRing sq.sq.R → Subsingleton sq.commSq.LiftStruct

/-- Restricted DVR uniqueness is equivalent to every factored DVR valuative square
having at most one dotted lift. -/
theorem uniqueness_iff {S : Scheme.{u}} {U X Y : AlgebraicSpace S} (h : U ⟶ X)
    (f : X ⟶ Y) :
    Uniqueness h f ↔
      ∀ sq : ValuativeCommSqFactorsThrough h f,
        IsDiscreteValuationRing sq.sq.R → Subsingleton sq.commSq.LiftStruct :=
  sorry

/-- Restricted DVR uniqueness follows from at most one lift in every factored DVR
valuative square. -/
theorem uniqueness_of {S : Scheme.{u}} {U X Y : AlgebraicSpace S} {h : U ⟶ X} {f : X ⟶ Y}
    (h_uniqueness :
      ∀ sq : ValuativeCommSqFactorsThrough h f,
        IsDiscreteValuationRing sq.sq.R → Subsingleton sq.commSq.LiftStruct) :
    Uniqueness h f :=
  sorry

/-- Restricted DVR uniqueness supplies at most one dotted lift of a factored DVR
valuative square. -/
theorem uniqueness {S : Scheme.{u}} {U X Y : AlgebraicSpace S} {h : U ⟶ X}
    {f : X ⟶ Y} (h_uniqueness : Uniqueness h f)
    (sq : ValuativeCommSqFactorsThrough h f)
    (hR : IsDiscreteValuationRing sq.sq.R) :
    Subsingleton sq.commSq.LiftStruct :=
  sorry

/-- Unrestricted DVR uniqueness implies DVR uniqueness along any morphism. -/
theorem uniqueness_of_dvrUniqueness {S : Scheme.{u}} {U X Y : AlgebraicSpace S}
    (h : U ⟶ X) (f : X ⟶ Y) [ValuativeCriterion.DVR.Uniqueness f] :
    Uniqueness h f :=
  sorry

end ValuativeCriterion.DVR.Along

end AlgebraicGeometry.AlgebraicSpace
