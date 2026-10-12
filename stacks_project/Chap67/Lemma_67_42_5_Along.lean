/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_41_1_ValuativeCriterion

/-!
# Valuative squares of algebraic spaces with factored generic arrows

This module packages valuative squares whose generic arrow is equipped with a
factorization through a fixed morphism of algebraic spaces, together with the
restricted uniqueness and existence predicates used by the refined valuative
criterion for universal closedness.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A valuative commutative square for `f` whose generic arrow factors through
`h`. -/
structure ValuativeCommSqFactorsThrough {S : Scheme.{u}} {U X Y : AlgebraicSpace S}
    (h : U ⟶ X) (f : X ⟶ Y) where
  /-- The underlying valuative commutative square over `f`. -/
  sq : ValuativeCommSq f
  /-- A chosen factorization of the generic arrow through `h`. -/
  genericToSource : ofOver sq.specK ⟶ U
  /-- The chosen generic factorization composes to the generic arrow of `sq`. -/
  fac : genericToSource ≫ h = sq.i₁

namespace ValuativeCommSqFactorsThrough

/-- Equip a valuative commutative square with a chosen factorization of its
generic arrow through `h`. -/
def of {S : Scheme.{u}} {U X Y : AlgebraicSpace S} {h : U ⟶ X} {f : X ⟶ Y}
    (sq : ValuativeCommSq f) (genericToSource : ofOver sq.specK ⟶ U)
    (fac : genericToSource ≫ h = sq.i₁) : ValuativeCommSqFactorsThrough h f where
  sq := sq
  genericToSource := genericToSource
  fac := fac

/-- The underlying commutative square of a factored valuative square. -/
abbrev commSq {S : Scheme.{u}} {U X Y : AlgebraicSpace S} {h : U ⟶ X} {f : X ⟶ Y}
    (sq : ValuativeCommSqFactorsThrough h f) :=
  sq.sq.commSq

/-- The packaged square of `ValuativeCommSqFactorsThrough.of` is the given
valuative square. -/
theorem of_sq {S : Scheme.{u}} {U X Y : AlgebraicSpace S} {h : U ⟶ X} {f : X ⟶ Y}
    (sq : ValuativeCommSq f) (genericToSource : ofOver sq.specK ⟶ U)
    (fac : genericToSource ≫ h = sq.i₁) : (of sq genericToSource fac).sq = sq :=
  sorry

/-- The generic factorization of `ValuativeCommSqFactorsThrough.of` is the given
morphism `Spec(K) ⟶ U`. -/
theorem of_genericToSource {S : Scheme.{u}} {U X Y : AlgebraicSpace S}
    {h : U ⟶ X} {f : X ⟶ Y} (sq : ValuativeCommSq f)
    (genericToSource : ofOver sq.specK ⟶ U) (fac : genericToSource ≫ h = sq.i₁) :
    (of sq genericToSource fac).genericToSource = genericToSource :=
  sorry

/-- The generic factorization of `ValuativeCommSqFactorsThrough.of` composes to
the generic arrow of the given valuative square. -/
theorem of_fac {S : Scheme.{u}} {U X Y : AlgebraicSpace S} {h : U ⟶ X} {f : X ⟶ Y}
    (sq : ValuativeCommSq f) (genericToSource : ofOver sq.specK ⟶ U)
    (fac : genericToSource ≫ h = sq.i₁) :
    (of sq genericToSource fac).genericToSource ≫ h = sq.i₁ :=
  sorry

/-- The generic arrow of a factored valuative square is the composition
`Spec(K) ⟶ U ⟶ X`. -/
theorem spec {S : Scheme.{u}} {U X Y : AlgebraicSpace S} {h : U ⟶ X} {f : X ⟶ Y}
    (sq : ValuativeCommSqFactorsThrough h f) :
    sq.genericToSource ≫ h = sq.sq.i₁ :=
  sorry

/-- The underlying commutative square of a factored valuative square is the
commutative square of the packaged valuative square. -/
theorem commSq_eq {S : Scheme.{u}} {U X Y : AlgebraicSpace S} {h : U ⟶ X}
    {f : X ⟶ Y} (sq : ValuativeCommSqFactorsThrough h f) :
    sq.commSq = sq.sq.commSq :=
  sorry

end ValuativeCommSqFactorsThrough

namespace ValuativeCriterion.Along

/-- Every valuative square whose generic arrow factors through `h` has at most
one dotted lift `Spec(A) ⟶ X`. -/
def Uniqueness {S : Scheme.{u}} {U X Y : AlgebraicSpace S} (h : U ⟶ X)
    (f : X ⟶ Y) : Prop :=
  ∀ sq : ValuativeCommSqFactorsThrough h f, Subsingleton sq.commSq.LiftStruct

/-- Every valuative square whose generic arrow factors through `h` admits a
dominating valuation-ring extension together with a lift of the extended
square. -/
def Existence {S : Scheme.{u}} {U X Y : AlgebraicSpace S} (h : U ⟶ X)
    (f : X ⟶ Y) : Prop :=
  ∀ sq : ValuativeCommSqFactorsThrough h f, Nonempty sq.sq.Extension

/-- Restricted uniqueness is equivalent to every factored valuative square having
at most one dotted lift. -/
theorem uniqueness_iff {S : Scheme.{u}} {U X Y : AlgebraicSpace S} (h : U ⟶ X)
    (f : X ⟶ Y) :
    Uniqueness h f ↔
      ∀ sq : ValuativeCommSqFactorsThrough h f, Subsingleton sq.commSq.LiftStruct :=
  sorry

/-- Restricted uniqueness supplies at most one dotted lift of a factored
valuative square. -/
theorem uniqueness {S : Scheme.{u}} {U X Y : AlgebraicSpace S} {h : U ⟶ X}
    {f : X ⟶ Y} (h_uniqueness : Uniqueness h f)
    (sq : ValuativeCommSqFactorsThrough h f) :
    Subsingleton sq.commSq.LiftStruct :=
  sorry

/-- Restricted existence is equivalent to every factored valuative square
admitting a dominating extension with a lift. -/
theorem existence_iff {S : Scheme.{u}} {U X Y : AlgebraicSpace S} (h : U ⟶ X)
    (f : X ⟶ Y) :
    Existence h f ↔
      ∀ sq : ValuativeCommSqFactorsThrough h f, Nonempty sq.sq.Extension :=
  sorry

/-- Restricted existence supplies a dominating extension with a lift of a
factored valuative square. -/
theorem existence {S : Scheme.{u}} {U X Y : AlgebraicSpace S} {h : U ⟶ X}
    {f : X ⟶ Y} (h_existence : Existence h f)
    (sq : ValuativeCommSqFactorsThrough h f) :
    Nonempty sq.sq.Extension :=
  sorry

/-- Uniqueness of dotted lifts in every valuative square implies uniqueness along
any morphism. -/
theorem uniqueness_of_valuativeCriterion {S : Scheme.{u}}
    {U X Y : AlgebraicSpace S} (h : U ⟶ X) (f : X ⟶ Y)
    [ValuativeCriterion.Uniqueness f] : Uniqueness h f :=
  sorry

/-- Existence of a dominating extension for every valuative square implies
existence along any morphism. -/
theorem existence_of_valuativeCriterion {S : Scheme.{u}}
    {U X Y : AlgebraicSpace S} (h : U ⟶ X) (f : X ⟶ Y)
    [ValuativeCriterion.Existence f] : Existence h f :=
  sorry

end ValuativeCriterion.Along

end AlgebraicGeometry.AlgebraicSpace
