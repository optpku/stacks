/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.ReesAlgebra.Integral
import StacksCheckRecall

@[expose] public section

/-! @stack 00H3 -/

/-!
# Lemma 10.38.2

The reusable owner uses an explicit map from the Rees algebra to the target
polynomial ring, avoiding local polynomial-algebra instances.
-/

/- Lemma 10.38.2 (Tag 00H3): ideal-relative integrality is integrality of
`C g * X` over the Rees algebra. -/
@[stacks 00H3]
#check @RingHom.isIntegralOverIdeal_iff_rees

@[stacks 00H3 "Rees polynomial map"]
#check @ReesAlgebra.polynomialMap

@[stacks 00H3 "Rees polynomial map evaluation"]
#check @ReesAlgebra.polynomialMap_apply
