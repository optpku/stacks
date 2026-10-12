/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.FieldTheory.Separable.DiagonalLocalization
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.43.8

Lemma 10.43.8 (Tag 0C2X) is a canonical recall of the localization form of
tensor-square multiplication for a separable algebraic field extension.
The reusable owner is `Algebra.IsSeparable`, not a Chapter 10 proof route.

@stack 0C2X
-/

@[stacks 0C2X]
#check @Algebra.IsSeparable.exists_lmul_isLocalization
