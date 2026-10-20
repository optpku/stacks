/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ValuativeCriterion.DVR
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ValuativeCriterion.Factorization
import Mathlib.Tactic.CrossRefAttribute

/-!
# DVR-valuative squares with factored generic arrows

This leaf restricts `ValuativeCommSqFactorsThrough` to discrete valuation
rings and supplies the corresponding existence, uniqueness, and combined
criteria.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- A valuative square whose generic arrow factors through `h` and whose valuation ring is a
discrete valuation ring. -/
@[stacks 0CM3 "DVR-valuative square with a factored generic map"]
abbrev DvrValuativeCommSqFactorsThrough {U X S : Scheme.{u}} (h : U ⟶ X) (f : X ⟶ S) :
    Type (u + 1) :=
  { sq : ValuativeCommSqFactorsThrough h f // IsDiscreteValuationRing sq.sq.R }

namespace DvrValuativeCommSqFactorsThrough

/-- The underlying unrestricted valuative commutative square. -/
abbrev toValuativeCommSq {U X S : Scheme.{u}} {h : U ⟶ X} {f : X ⟶ S}
    (sq : DvrValuativeCommSqFactorsThrough h f) : ValuativeCommSq f :=
  sq.val.sq

/-- The underlying DVR-valuative commutative square. -/
abbrev toDvrValuativeCommSq {U X S : Scheme.{u}} {h : U ⟶ X} {f : X ⟶ S}
    (sq : DvrValuativeCommSqFactorsThrough h f) : DvrValuativeCommSq f :=
  ⟨sq.toValuativeCommSq, sq.property⟩

/-- The underlying commutative square. -/
abbrev commSq {U X S : Scheme.{u}} {h : U ⟶ X} {f : X ⟶ S}
    (sq : DvrValuativeCommSqFactorsThrough h f) :=
  sq.toDvrValuativeCommSq.commSq

/-- The chosen factorization of the generic arrow through `h`. -/
abbrev genericToSource {U X S : Scheme.{u}} {h : U ⟶ X} {f : X ⟶ S}
    (sq : DvrValuativeCommSqFactorsThrough h f) :=
  sq.val.genericToSource

/-- The chosen generic factorization composes to the generic arrow of the underlying square. -/
abbrev fac {U X S : Scheme.{u}} {h : U ⟶ X} {f : X ⟶ S}
    (sq : DvrValuativeCommSqFactorsThrough h f) :=
  sq.val.fac

/-- The valuation ring of a factored DVR-valuative square is canonically a discrete valuation
ring. -/
instance instIsDiscreteValuationRing {U X S : Scheme.{u}} {h : U ⟶ X} {f : X ⟶ S}
    (sq : DvrValuativeCommSqFactorsThrough h f) :
    IsDiscreteValuationRing sq.toValuativeCommSq.R := sorry

end DvrValuativeCommSqFactorsThrough

/- DVR-valuative criteria restricted to squares with a chosen generic factorization. -/
namespace ValuativeCriterion.DVR.Along

/-- Every factored DVR-valuative square over `f` admits a lift. -/
@[stacks 0CM3 "factored DVR valuative existence criterion"]
def Existence {U X S : Scheme.{u}} (h : U ⟶ X) (f : X ⟶ S) : Prop :=
  ∀ sq : DvrValuativeCommSqFactorsThrough h f, sq.commSq.HasLift

/-- Every factored DVR-valuative square over `f` has at most one lift. -/
@[stacks 0CM4 "factored DVR valuative uniqueness criterion"]
def Uniqueness {U X S : Scheme.{u}} (h : U ⟶ X) (f : X ⟶ S) : Prop :=
  ∀ sq : DvrValuativeCommSqFactorsThrough h f, Subsingleton sq.commSq.LiftStruct

/-- Every factored DVR-valuative square over `f` has a lift and at most one lift. -/
@[stacks 0CM5 "factored DVR valuative exists-unique criterion"]
def ExistsUnique {U X S : Scheme.{u}} (h : U ⟶ X) (f : X ⟶ S) : Prop :=
  ∀ sq : DvrValuativeCommSqFactorsThrough h f,
    sq.commSq.HasLift ∧ Subsingleton sq.commSq.LiftStruct

/-- Factored DVR existence-and-uniqueness is equivalent to its separate existence and uniqueness
conditions. -/
@[stacks 0CM5 "factored DVR valuative criterion decomposition"]
theorem existsUnique_iff {U X S : Scheme.{u}} {h : U ⟶ X} {f : X ⟶ S} :
    ExistsUnique h f ↔ Existence h f ∧ Uniqueness h f := sorry

/-- Factored DVR existence-and-uniqueness implies factored DVR existence. -/
@[stacks 0CM3 "factored DVR valuative existence projection"]
theorem existence {U X S : Scheme.{u}} {h : U ⟶ X} {f : X ⟶ S}
    (h_criterion : ExistsUnique h f) : Existence h f := sorry

/-- Factored DVR existence-and-uniqueness implies factored DVR uniqueness. -/
@[stacks 0CM4 "factored DVR valuative uniqueness projection"]
theorem uniqueness {U X S : Scheme.{u}} {h : U ⟶ X} {f : X ⟶ S}
    (h_criterion : ExistsUnique h f) : Uniqueness h f := sorry

end ValuativeCriterion.DVR.Along

end AlgebraicGeometry
