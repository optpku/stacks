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
Lemma 10.158.8: canonical recalls for field extensions.  Part `(1)` is the
characteristic-zero specialization owned by `Algebra.formallySmooth_of_charZero`.
Part `(2)` keeps the source's positive-characteristic hypothesis through the
`Algebra.FormallySmooth.CharP` bridge; the unrestricted equivalence is retained
as a stronger all-characteristic companion.

@stack 0321
-/

@[stacks 0321 "(1)"]
#check @Algebra.formallySmooth_of_charZero

@[stacks 0321 "(2)"]
#check @Algebra.FormallySmooth.CharP.iff_isSeparableOver

#check @Algebra.formallySmooth_iff_isSeparableOver
