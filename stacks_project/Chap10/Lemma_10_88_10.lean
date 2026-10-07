module

import StacksCheckRecall
public import ReasLib.RingTheory.Flatness.MittagLeffler.FiniteFree

@[expose] public section

/-!
Chapter 10, Lemma 10.88.10 is the finite-free detection criterion for Mittag-Leffler modules.
The reusable API also exposes the reduction from finitely presented sources and both logical
directions separately.

@stack 05CP
-/

@[stacks 05CP]
#check Module.MittagLeffler.FiniteFree.iff_kernelFactorization

@[stacks 05CP "finite-free kernel-factorization data"]
#check @Module.MittagLeffler.FiniteFree.KernelFactorization

@[stacks 05CP "finite-kernel equivalence"]
#check @Module.MittagLeffler.FiniteKernelFactorization.iff_finiteFree

@[stacks 05CP "kernel factorization from Mittag-Leffler"]
#check @Module.MittagLeffler.FiniteFree.KernelFactorization.of_mittagLeffler

@[stacks 05CP "Mittag-Leffler from kernel factorization"]
#check @Module.MittagLeffler.FiniteFree.KernelFactorization.mittagLeffler
