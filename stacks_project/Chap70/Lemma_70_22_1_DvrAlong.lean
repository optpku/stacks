module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import stacks_project.Chap67.Lemma_67_42_5_Along
public import stacks_project.Chap69.Lemma_69_19_2_DVR

/-!
# DVR valuative existence along a morphism of algebraic spaces

A morphism of algebraic spaces satisfies the existence part of the DVR
valuative criterion along a second morphism when every valuative square whose
generic arrow factors through that morphism, and whose ring is a discrete
valuation ring, admits a dotted lift.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace ValuativeCriterion.DVR.Along

/-- Every valuative square whose generic arrow factors through `h` and whose ring
is a discrete valuation ring admits a dotted lift `Spec(A) ⟶ X`. -/
def Existence {S : Scheme.{u}} {U X Y : AlgebraicSpace S} (h : U ⟶ X)
    (f : X ⟶ Y) : Prop :=
  ∀ sq : ValuativeCommSqFactorsThrough h f,
    IsDiscreteValuationRing sq.sq.R → sq.commSq.HasLift

/-- Restricted DVR existence is equivalent to every factored DVR valuative square
having a dotted lift. -/
theorem existence_iff {S : Scheme.{u}} {U X Y : AlgebraicSpace S} (h : U ⟶ X)
    (f : X ⟶ Y) :
    Existence h f ↔
      ∀ sq : ValuativeCommSqFactorsThrough h f,
        IsDiscreteValuationRing sq.sq.R → sq.commSq.HasLift :=
  sorry

/-- Restricted DVR existence follows from a lift in every factored DVR valuative
square. -/
theorem of {S : Scheme.{u}} {U X Y : AlgebraicSpace S} {h : U ⟶ X} {f : X ⟶ Y}
    (h_existence :
      ∀ sq : ValuativeCommSqFactorsThrough h f,
        IsDiscreteValuationRing sq.sq.R → sq.commSq.HasLift) :
    Existence h f :=
  sorry

/-- Restricted DVR existence supplies a dotted lift of a factored DVR valuative
square. -/
theorem existence {S : Scheme.{u}} {U X Y : AlgebraicSpace S} {h : U ⟶ X}
    {f : X ⟶ Y} (h_existence : Existence h f)
    (sq : ValuativeCommSqFactorsThrough h f)
    (hR : IsDiscreteValuationRing sq.sq.R) :
    sq.commSq.HasLift :=
  sorry

/-- Unrestricted DVR existence implies DVR existence along any morphism. -/
theorem existence_of_dvrExistence {S : Scheme.{u}} {U X Y : AlgebraicSpace S}
    (h : U ⟶ X) (f : X ⟶ Y) [ValuativeCriterion.DVR.Existence f] :
    Existence h f :=
  sorry

end ValuativeCriterion.DVR.Along

end AlgebraicGeometry.AlgebraicSpace
