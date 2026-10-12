/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-!
# Valuative squares with factored generic arrows

This leaf packages valuative squares whose generic arrow is equipped with a
factorization through a fixed scheme morphism. It applies to arbitrary
valuation rings; DVR restrictions live in the sibling `DVR` namespace.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- A valuative commutative square for `f` whose generic arrow factors through `h`. -/
structure ValuativeCommSqFactorsThrough {U X S : Scheme.{u}} (h : U ⟶ X) (f : X ⟶ S) where
  /-- The underlying valuative commutative square over `f`. -/
  sq : ValuativeCommSq f
  /-- A chosen factorization of the generic arrow through `h`. -/
  genericToSource : Spec (CommRingCat.of sq.K) ⟶ U
  /-- The chosen generic factorization composes to the generic arrow of `sq`. -/
  fac : genericToSource ≫ h = sq.i₁

namespace ValuativeCommSqFactorsThrough

/-- Equip a valuative commutative square with a chosen factorization of its generic arrow
through `h`. -/
def ofValuativeCommSq {U X S : Scheme.{u}} {h : U ⟶ X} {f : X ⟶ S}
    (sq : ValuativeCommSq f) (genericToSource : Spec (CommRingCat.of sq.K) ⟶ U)
    (fac : genericToSource ≫ h = sq.i₁) : ValuativeCommSqFactorsThrough h f :=
  { sq := sq, genericToSource := genericToSource, fac := fac }

/-- The underlying commutative square. -/
abbrev commSq {U X S : Scheme.{u}} {h : U ⟶ X} {f : X ⟶ S}
    (sq : ValuativeCommSqFactorsThrough h f) :=
  sq.sq.commSq

end ValuativeCommSqFactorsThrough

/- Valuative criteria restricted to squares with a chosen generic factorization. -/
namespace ValuativeCriterion.Along

/-- Every valuative square whose generic arrow factors through `h` admits a lift. -/
def Existence {U X S : Scheme.{u}} (h : U ⟶ X) (f : X ⟶ S) : Prop :=
  ∀ sq : ValuativeCommSqFactorsThrough h f, sq.commSq.HasLift

/-- Every valuative square whose generic arrow factors through `h` has at most one lift. -/
def Uniqueness {U X S : Scheme.{u}} (h : U ⟶ X) (f : X ⟶ S) : Prop :=
  ∀ sq : ValuativeCommSqFactorsThrough h f, Subsingleton sq.commSq.LiftStruct

/-- Every valuative square whose generic arrow factors through `h` has a lift and at most one
lift. -/
def ExistsUnique {U X S : Scheme.{u}} (h : U ⟶ X) (f : X ⟶ S) : Prop :=
  ∀ sq : ValuativeCommSqFactorsThrough h f,
    sq.commSq.HasLift ∧ Subsingleton sq.commSq.LiftStruct

/-- Restricted valuative existence-and-uniqueness is equivalent to its separate existence and
uniqueness conditions. -/
theorem existsUnique_iff {U X S : Scheme.{u}} {h : U ⟶ X} {f : X ⟶ S} :
    ExistsUnique h f ↔ Existence h f ∧ Uniqueness h f := sorry

/-- Restricted valuative existence-and-uniqueness implies restricted valuative existence. -/
theorem existence {U X S : Scheme.{u}} {h : U ⟶ X} {f : X ⟶ S}
    (h_criterion : ExistsUnique h f) : Existence h f := sorry

/-- Restricted valuative existence-and-uniqueness implies restricted valuative uniqueness. -/
theorem uniqueness {U X S : Scheme.{u}} {h : U ⟶ X} {f : X ⟶ S}
    (h_criterion : ExistsUnique h f) : Uniqueness h f := sorry

/-- A separated morphism has at most one lift in every valuative square whose generic arrow
factors through a fixed morphism. -/
theorem uniqueness_of_isSeparated {U X S : Scheme.{u}} (f : X ⟶ S) (h : U ⟶ X)
    [IsSeparated f] : Uniqueness h f := sorry

end ValuativeCriterion.Along

end AlgebraicGeometry
