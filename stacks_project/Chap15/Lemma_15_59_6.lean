/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.CochainComplex.KFlat.ShortExact

/-!
# Lemma 15.59.6

@stack 0BYH

The three source-facing two-out-of-three implications are owned by
`CategoryTheory.ShortComplex.ShortExact.isKFlat_X₁`, `isKFlat_X₂`, and `isKFlat_X₃`.
-/

@[expose] public section

/- Lemma 15.59.6 (1): K-flatness of the first two terms implies K-flatness of the right term. -/
@[stacks 0BYH "K-flat short exact sequences, right term"]
#check @CategoryTheory.ShortComplex.ShortExact.isKFlat_X₃

/- Lemma 15.59.6 (2): K-flatness of the outer terms implies K-flatness of the middle term. -/
@[stacks 0BYH "K-flat short exact sequences, middle term"]
#check @CategoryTheory.ShortComplex.ShortExact.isKFlat_X₂

/- Lemma 15.59.6 (3): K-flatness of the last two terms implies K-flatness of the left term. -/
@[stacks 0BYH "K-flat short exact sequences, left term"]
#check @CategoryTheory.ShortComplex.ShortExact.isKFlat_X₁
