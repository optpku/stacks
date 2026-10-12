/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Unramified.Basic
import StacksCheckRecall

@[expose] public section

/-!
# Definition 10.148.1

@stack 00UN
-/

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 10.148.1: for a ring map `R → S`, the statement that `S` is formally unramified
over `R` is the canonical mathlib predicate `Algebra.FormallyUnramified R S`. -/
@[stacks 00UN "formally unramified predicate"]
#check @Algebra.FormallyUnramified

/- Companion recall: the infinitesimal lifting formulation in the text is the existing theorem
`Algebra.FormallyUnramified.iff_comp_injective`, expressing formal unramifiedness as uniqueness of
lifts across square-zero thickenings. -/
@[stacks 00UN "formal unramified lifting criterion"]
#check @Algebra.FormallyUnramified.iff_comp_injective
