module

public import stacks_project.Chap70.Lemma_70_22_1_DvrAlong
public import stacks_project.Chap70.Lemma_70_22_2_DvrAlong

/-!
# Unique DVR lifts along a morphism of algebraic spaces

A morphism of algebraic spaces satisfies the unique-lift form of the DVR
valuative criterion along a second morphism when every valuative square whose
generic arrow factors through that morphism, and whose ring is a discrete
valuation ring, admits exactly one dotted lift.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace ValuativeCriterion.DVR.Along

/-- Every valuative square whose generic arrow factors through `h` and whose ring
is a discrete valuation ring admits a unique dotted lift `Spec(A) ⟶ X`. -/
def ExistsUnique {S : Scheme.{u}} {U X Y : AlgebraicSpace S} (h : U ⟶ X)
    (f : X ⟶ Y) : Prop :=
  ∀ sq : ValuativeCommSqFactorsThrough h f,
    IsDiscreteValuationRing sq.sq.R →
      sq.commSq.HasLift ∧ Subsingleton sq.commSq.LiftStruct

/-- Restricted unique DVR lifts are equivalent to restricted DVR existence and
uniqueness. -/
theorem existsUnique_iff {S : Scheme.{u}} {U X Y : AlgebraicSpace S} (h : U ⟶ X)
    (f : X ⟶ Y) : ExistsUnique h f ↔ Existence h f ∧ Uniqueness h f :=
  sorry

namespace ExistsUnique

/-- Restricted unique DVR lifts follow from a unique dotted lift in every
factored DVR valuative square. -/
theorem of {S : Scheme.{u}} {U X Y : AlgebraicSpace S} {h : U ⟶ X} {f : X ⟶ Y}
    (h_existsUnique :
      ∀ sq : ValuativeCommSqFactorsThrough h f,
        IsDiscreteValuationRing sq.sq.R →
          sq.commSq.HasLift ∧ Subsingleton sq.commSq.LiftStruct) :
    ExistsUnique h f :=
  sorry

/-- Restricted unique DVR lifts imply DVR existence along `h`. -/
theorem existence {S : Scheme.{u}} {U X Y : AlgebraicSpace S} {h : U ⟶ X}
    {f : X ⟶ Y} (h_existsUnique : ExistsUnique h f) : Existence h f :=
  sorry

/-- Restricted unique DVR lifts imply DVR uniqueness along `h`. -/
theorem uniqueness {S : Scheme.{u}} {U X Y : AlgebraicSpace S} {h : U ⟶ X}
    {f : X ⟶ Y} (h_existsUnique : ExistsUnique h f) : Uniqueness h f :=
  sorry

end ExistsUnique

end ValuativeCriterion.DVR.Along

end AlgebraicGeometry.AlgebraicSpace
