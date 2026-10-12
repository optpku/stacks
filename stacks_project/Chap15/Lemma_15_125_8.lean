/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.Bezout
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.125.8

@stack 0ASU

The reusable content is owned by the Bezout-module leaf.  The chapter entry
records the finite-free result, the canonical torsion splitting, and the finite
cyclic-quotient retract without retaining a chapter-local proof infrastructure.
-/

/- Lemma 15.125.8 (1): finite submodules of free modules are finite free. -/
@[stacks 0ASU "Lemma 15.125.8 (1), finite submodules of free modules"]
#check @Submodule.freeOfFiniteOfIsBezout

/- Lemma 15.125.8 (2), finite-free quotient clause: the quotient by torsion is finite free. -/
@[stacks 0ASU "Lemma 15.125.8 (2), finite-free quotient clause"]
#check @Module.FinitePresentation.torsionQuotientFree

/- Lemma 15.125.8 (3), splitting clause: a finitely presented module splits into its finite free
quotient and torsion submodule. -/
@[stacks 0ASU "Lemma 15.125.8 (3), splitting clause"]
#check @Module.FinitePresentation.torsionSplit

/- Lemma 15.125.8 (4), cyclic-retract clause: the torsion part is a summand of finitely many
nonzero principal cyclic quotients. -/
@[stacks 0ASU "Lemma 15.125.8 (4), cyclic-retract clause"]
#check @Module.FinitePresentation.existsTorsionCyclicRetract

#check @Module.IsTorsionFree.freeOfFiniteOfIsBezout
#check @Module.Finite.torsionQuotientFree
#check @Module.Finite.torsionSplit
