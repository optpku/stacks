/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.FieldTheory.Separable.Generated.Properties
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.44.3

Lemma 10.44.3 (Tag 030X) is a canonical recall of
`Algebra.IsSeparablyGenerated.isSeparableOver`: a separably generated field
extension is separable over its base in the sense of Definition 10.42.1 (2).

@stack 030X
-/

@[stacks 030X]
#check @Algebra.IsSeparablyGenerated.isSeparableOver
