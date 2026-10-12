/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.GoingUp.Incomparability
import StacksCheckRecall

/-!
# Incomparability in an Integral Fiber

@stack 00GT
-/

@[expose] public section

@[stacks 00GT "strict contraction along an integral ring homomorphism"]
#check @RingHom.IsIntegral.comap_lt_comap

@[stacks 00GT "incomparability in an integral spectrum fiber"]
#check @PrimeSpectrum.incompRel_of_comap_eq_of_isIntegral

@[stacks 00GT "integral spectrum fibers are antichains"]
#check @PrimeSpectrum.isAntichain_comap_fiber_of_isIntegral
