/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Flatness.AssociatedGraded
import StacksCheckRecall

/-!
# Flatness modulo powers of an ideal

@stack 0AS8

Lemma 10.99.9 gives flatness modulo `I ^ 2`, and more generally modulo
`I ^ (k + 1)`, from flatness modulo `I` and injectivity of the canonical maps
to the associated graded pieces.
-/

@[expose] public section

@[stacks 0AS8 "canonical tensor map"]
#check @Ideal.AssociatedGraded.tensorToPiece

@[stacks 0AS8 "canonical tensor map on pure tensors"]
#check @Ideal.AssociatedGraded.tensorToPiece_tmul_mk

@[stacks 0AS8 "(1)"]
#check @Module.Flat.AssociatedGraded.modIdealSq_of_tensorToPiece_injective

@[stacks 0AS8 "(2)"]
#check @Module.Flat.AssociatedGraded.modIdealPowSucc_of_tensorToPiece_injective
