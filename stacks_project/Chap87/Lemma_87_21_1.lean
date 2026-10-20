module

public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Topology.Adic.Complete
public import stacks_project.Chap87.Definition_87_7_1_WeaklyAdic
public import stacks_project.Chap87.«87_21_2_1_LocalizeSquare»
public import ReasLib.RingTheory.Topology.WeakIdealCompletion.Properties
import StacksCheckRecall

/-!
# Lemma 87.21.1

Weak-ideal completion along an untopologized algebra map preserves membership
in the countably indexed, admissible, weakly adic, adic*, and Noetherian adic
full subcategories of weakly admissible rings.
-/

@[expose] public section

universe u

open TopologicalRing

variable {A A' : Type u}
variable [CommRing A] [TopologicalSpace A] [CommRing A'] [Algebra A A']

/- Lemma 87.21.1 (1): weak-ideal completion preserves countable indexing. -/
@[stacks 0ANB] #check (TopologicalRing.weakIdealCompletion.instIsCountablyIndexed :
  ∀ [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A],
    IsCountablyIndexed (weakIdealCompletion A A'))

/- Part (2): together with countability from (1), preservation of admissibility
gives preservation of countably indexed admissibility. -/
#check (TopologicalRing.weakIdealCompletion.instIsAdmissibleRing :
  ∀ [IsAdmissibleRing A], IsAdmissibleRing (weakIdealCompletion A A'))

/- Part (3): weak-ideal completion preserves weak adicity. -/
#check (TopologicalRing.weakIdealCompletion.instIsWeaklyAdicRing :
  ∀ [IsWeaklyAdicRing A], IsWeaklyAdicRing (weakIdealCompletion A A'))

/- Part (4): preservation of adic* uses both adicity and existence of a finitely
generated ideal of definition, on both the input and the completion. -/
#check (TopologicalRing.weakIdealCompletion.isAdicRing :
  ∀ [IsAdicRing A], (∃ I : Ideal A, I.FG ∧ Ideal.IsIdealOfDefinition I) →
    IsAdicRing (weakIdealCompletion A A'))

#check (TopologicalRing.weakIdealCompletion.exists_fg_isIdealOfDefinition :
  ∀ [IsAdicRing A], (∃ I : Ideal A, I.FG ∧ Ideal.IsIdealOfDefinition I) →
    ∃ J : Ideal (weakIdealCompletion A A'), J.FG ∧ Ideal.IsIdealOfDefinition J)

/- Part (5): the completion of a Noetherian algebra over a Noetherian adic ring
is Noetherian and adic. -/
#check (TopologicalRing.weakIdealCompletion.instIsNoetherianRing :
  ∀ [IsAdicRing A] [IsNoetherianRing A] [IsNoetherianRing A'],
    IsNoetherianRing (weakIdealCompletion A A'))

#check (TopologicalRing.weakIdealCompletion.isAdicRing_and_isNoetherianRing :
  ∀ [IsAdicRing A] [IsNoetherianRing A] [IsNoetherianRing A'],
    IsAdicRing (weakIdealCompletion A A') ∧ IsNoetherianRing (weakIdealCompletion A A'))
