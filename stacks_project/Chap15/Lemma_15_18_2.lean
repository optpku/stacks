/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Flat.Locus.Descent
import StacksCheckRecall

/-!
# Descent of the closed-fiber flatness condition

Lemma 15.18.2 is the closed-subset descent theorem for a tensor-product base change.

@stack 05LL
-/

@[stacks 05LL "Lemma 15.18.2"]
#check @Ideal.FlatLocus.tensorBaseChange_descends

@[stacks 05LL "compatible prime of a tensor product"]
#check @Algebra.TensorProduct.existsPrimeOver

@[stacks 05LL "localized flatness descent through tensor base change"]
#check @Module.Flat.localized_of_tensorBaseChange

@[stacks 05LL "fiber of a tensor-product base change"]
#check @Algebra.TensorProduct.fiberRightAlgEquiv
