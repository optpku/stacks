module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.Factorization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR

/-!
# DVR valuative existence and uniqueness along a morphism of algebraic spaces

The existence and uniqueness parts of the DVR valuative criterion along a
morphism concern dotted lifts of valuative squares whose generic arrow factors
through that morphism and whose ring is a discrete valuation ring.
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
