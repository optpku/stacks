/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.FieldTheory.Separable.Conormal
import StacksCheckRecall

@[expose] public section

/-!
Lemma 10.140.4 [stacks 00TU]: canonical recall of the separable
residue-field conormal injectivity bridge.

@stack 00TU
-/

@[stacks 00TU]
#check @Algebra.IsSeparableOver.Conormal.residueField_injective
