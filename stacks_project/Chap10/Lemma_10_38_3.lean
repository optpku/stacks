/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.ReesAlgebra.Integral
import StacksCheckRecall

@[expose] public section

/-! @stack 00H4 -/

/-!
# Lemma 10.38.3

The additive and scalar closure API is owned by
`ReasLib.RingTheory.ReesAlgebra.Integral`.
-/

/- Lemma 10.38.3 (Tag 00H4): elements integral over an ideal form a submodule,
and multiplication by an ordinarily integral element preserves them. -/
@[stacks 00H4]
#check @RingHom.integralOverIdealSubmodule

#check @RingHom.mem_integralOverIdealSubmodule
#check @RingHom.isIntegralOverIdeal_zero
#check @RingHom.IsIntegralOverIdeal.add
#check @RingHom.IsIntegralOverIdeal.neg
#check @RingHom.IsIntegralOverIdeal.sub
#check @RingHom.IsIntegralOverIdeal.smul
#check @RingHom.IsIntegralElem.mul_isIntegralOverIdeal
