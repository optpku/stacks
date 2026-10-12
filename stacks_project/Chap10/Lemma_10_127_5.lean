/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DirectLimit.Algebra.BaseChange.FinitePresentation
import StacksCheckRecall

/-!
# Lemma 10.127.5

The four finite and finitely presented module descent statements are owned by
`Ring.DirectLimit.BaseChange`.  This source entry retains the Stacks label and
checks the complete shared declarations without creating chapter-level aliases.

@stack 05LI
-/

@[expose] public section

/- Lemma 10.127.5 (1), Stacks tag `05LI`: equality of base-changed maps out of
a finite module is witnessed at a stage. -/
@[stacks 05LI] #check @Ring.DirectLimit.BaseChange.Finite.exists_eq

/- Lemma 10.127.5 (2), Stacks tag `05LI`: surjectivity after base change onto a
finite module is witnessed at a stage. -/
@[stacks 05LI] #check @Ring.DirectLimit.BaseChange.Finite.exists_surjective

/- Lemma 10.127.5 (3), Stacks tag `05LI`: a map out of the base change of a
finitely presented module comes from a stage. -/
@[stacks 05LI] #check @Ring.DirectLimit.BaseChange.FinitePresentation.exists_stageMap

/- Lemma 10.127.5 (4), Stacks tag `05LI`: bijectivity after base change from a
finite module to a finitely presented module is witnessed at a stage. -/
@[stacks 05LI] #check @Ring.DirectLimit.BaseChange.FinitePresentation.exists_bijective
