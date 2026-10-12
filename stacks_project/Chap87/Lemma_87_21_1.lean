/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Topology.Adic.Complete
public import stacks_project.Chap87.Definition_87_7_1_WeaklyAdic
public import stacks_project.Chap87.«87_21_2_1_LocalizeSquare»

/-!
# Lemma 87.21.1

Weak-ideal completion along an untopologized algebra map preserves membership
in the countably indexed, admissible, weakly adic, adic*, and Noetherian adic
full subcategories of weakly admissible rings.
-/

@[expose] public section

universe u

open TopologicalRing

namespace TopologicalRing.weakIdealCompletion

variable {A A' : Type u}
variable [CommRing A] [TopologicalSpace A] [CommRing A'] [Algebra A A']

/-- Lemma 87.21.1 (1): if `A` is countably indexed and weakly admissible and
`A → A'` is a ring map with no topology on `A'`, then
`weakIdealCompletion A A'` is countably indexed. -/
@[stacks 0ANB, instance]
instance instIsCountablyIndexed [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A] :
    IsCountablyIndexed (weakIdealCompletion A A') := sorry

/-- Lemma 87.21.1 (2): if `A` is admissible and `A → A'` is a ring map with no
topology on `A'`, then `weakIdealCompletion A A'` is admissible. -/
@[stacks 0ANB, instance]
instance instIsAdmissibleRing [IsAdmissibleRing A] :
    IsAdmissibleRing (weakIdealCompletion A A') := sorry

/-- Lemma 87.21.1 (3): if `A` is weakly adic and `A → A'` is a ring map with no
topology on `A'`, then `weakIdealCompletion A A'` is weakly adic. -/
@[stacks 0ANB, instance]
instance instIsWeaklyAdicRing [IsWeaklyAdicRing A] :
    IsWeaklyAdicRing (weakIdealCompletion A A') := sorry

/-- Lemma 87.21.1 (4): if `A` is adic with a finitely generated ideal of
definition and `A → A'` is a ring map with no topology on `A'`, then
`weakIdealCompletion A A'` is adic. -/
@[stacks 0ANB]
theorem isAdicRing [IsAdicRing A]
    (hA : ∃ I : Ideal A, I.FG ∧ Ideal.IsIdealOfDefinition I) :
    IsAdicRing (weakIdealCompletion A A') := sorry

/-- The weak-ideal completion of an algebra over an adic ring with a finitely
generated ideal of definition again has a finitely generated ideal of
definition. -/
theorem exists_fg_isIdealOfDefinition [IsAdicRing A]
    (hA : ∃ I : Ideal A, I.FG ∧ Ideal.IsIdealOfDefinition I) :
    ∃ J : Ideal (weakIdealCompletion A A'), J.FG ∧ Ideal.IsIdealOfDefinition J :=
  sorry

/-- Lemma 87.21.1 (5): if `A` is a Noetherian adic ring, `A → A'` is a ring map
with no topology on `A'`, and `A'` is Noetherian, then
`weakIdealCompletion A A'` is Noetherian. -/
@[stacks 0ANB, instance]
instance instIsNoetherianRing [IsAdicRing A] [IsNoetherianRing A]
    [IsNoetherianRing A'] : IsNoetherianRing (weakIdealCompletion A A') := sorry

end TopologicalRing.weakIdealCompletion
