/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.BoundedAbove
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Model
import StacksCheckRecall

/-!
# Bounded-above termwise pseudo-coherence

Lemma 15.65.9 is owned by the absolute cochain-complex API in ReasLib; the truncation induction
belongs to the owner proof and is not duplicated here.

@stack 064Y
-/

@[expose] public section

/- Lemma 15.65.9 (1): the fixed `m` criterion. -/
@[stacks 064Y "(1), bounded-above m-pseudo-coherence"]
#check @CategoryTheory.CochainComplex.isMPseudoCoherent_of_boundedAbove_of_termwise

/- Lemma 15.65.9 (2): the pseudo-coherent specialization. -/
@[stacks 064Y "(2), bounded-above pseudo-coherence"]
#check @CategoryTheory.CochainComplex.IsPseudoCoherent.of_boundedAbove_of_termwise

#print axioms CategoryTheory.CochainComplex.isMPseudoCoherent_of_boundedAbove_of_termwise
#print axioms CategoryTheory.CochainComplex.IsPseudoCoherent.of_boundedAbove_of_termwise
