/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.AdicCompletion.Exactness.ShortComplex.Projective
import StacksCheckRecall

/-!
@stack 05D3

# Splitting completed short exact sequences

The reusable short-complex splitting and map-level section are owned by
`AdicCompletion`.  This source file only recalls the two interfaces.
-/

@[expose] public section

/- Lemma 10.97.9: completing a short exact sequence with flat cokernel and
projective closed fiber yields a split short complex. -/
@[stacks 05D3 "completed short-complex splitting"]
#check @AdicCompletion.mapShortComplex_splitting_of_flat_of_projective_quotient

/- The map-level companion produces a section of a completed surjection. -/
@[stacks 05D3 "completed map section"]
#check @AdicCompletion.map_has_section_of_flat_of_projective_quotient

#print axioms AdicCompletion.mapShortComplex_splitting_of_flat_of_projective_quotient
#print axioms AdicCompletion.map_has_section_of_flat_of_projective_quotient
