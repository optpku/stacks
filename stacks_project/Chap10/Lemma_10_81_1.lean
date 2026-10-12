/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Flatness.EquationalCriterion.FiniteFree
import StacksCheckRecall

/-!
# Lemma 10.81.1

@stack 058D
-/

@[expose] public section

@[stacks 058D "source four-clause form"]
#check @Module.Flat.FiniteFree.tfae

@[stacks 058D "single kernel-element criterion"]
#check @Module.Flat.FiniteFree.flat_iff_kernelFactorization

@[stacks 058D "one-element refinement criterion"]
#check @Module.Flat.FiniteFree.flat_iff_kernelRefinement

@[stacks 058D "finitely generated kernel criterion"]
#check @Module.Flat.FiniteFree.flat_iff_fgKernelFactorization

@[stacks 058D "finite-free factorization owner"]
#check @Module.Flat.exists_factorization_of_apply_eq_zero_of_free
