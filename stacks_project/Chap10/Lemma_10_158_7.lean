/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.FieldTheory.Separable.FormallySmooth
import StacksCheckRecall

@[expose] public section

/-!
Lemma 10.158.7 [stacks 0320]: canonical recall.  The purely
transcendental and Stacks-separable-over implications are reusable
field-theory statements; the separable-algebraic implication is the existing
mathlib formally-etale owner.

@stack 0320
-/

@[stacks 0320 "(1)"]
#check @Algebra.formallySmooth_of_purelyTranscendental

@[stacks 0320 "(2)"]
#check @Algebra.FormallyEtale.of_isSeparable

@[stacks 0320 "(3)"]
#check @Algebra.formallySmooth_of_isSeparableOver
