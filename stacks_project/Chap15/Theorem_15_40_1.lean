/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Smooth.Adic.GeometricRegularity
import StacksCheckRecall

/-!
# Theorem 15.40.1 (07EL)

@stack 07EL
-/

@[expose] public section

/- Theorem 15.40.1 (1) (07EL): the characteristic-zero criterion. -/
@[stacks 07EL "part 1, characteristic zero"]
#check @regularLocalRing_iff_formallySmooth_for_maximalIdeal_adic_of_charZero

/- Theorem 15.40.1 (2) (07EL): the positive-characteristic five-way criterion. -/
@[stacks 07EL "part 2, positive characteristic"]
#check @geometricallyRegular_formallySmooth_for_maximalIdeal_adic_tfae_of_charP
