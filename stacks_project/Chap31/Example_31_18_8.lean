/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Relative.Counterexample
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory
open scoped nonZeroDivisors

/- Example 31.18.8: For a field `k`, the explicit affine scheme over `k[t]` constructed from
generators `x` and `y n` has a relative effective Cartier divisor cut out by `x`, although its
ambient structural morphism is not flat on any open neighborhood of the divisor support. -/
@[stacks 062X] #check
  (AlgebraicGeometry.RelativeEffectiveCartierCounterexample.spec :
    ∀ (k : Type u) [Field k],
      AlgebraicGeometry.IsRelativeEffectiveCartierDivisor
        (AlgebraicGeometry.RelativeEffectiveCartierCounterexample.morphism k)
        (AlgebraicGeometry.RelativeEffectiveCartierCounterexample.divisor k) ∧
      ¬ ∃ U : (AlgebraicGeometry.RelativeEffectiveCartierCounterexample.scheme k).Opens,
        ((AlgebraicGeometry.RelativeEffectiveCartierCounterexample.divisor k).support :
            Set (AlgebraicGeometry.RelativeEffectiveCartierCounterexample.scheme k)) ⊆
          (U : Set (AlgebraicGeometry.RelativeEffectiveCartierCounterexample.scheme k)) ∧
          AlgebraicGeometry.Flat
            (U.ι ≫ AlgebraicGeometry.RelativeEffectiveCartierCounterexample.morphism k))

#check
  (AlgebraicGeometry.RelativeEffectiveCartierCounterexample.isRelativeEffectiveCartierDivisor :
    ∀ (k : Type u) [Field k],
      AlgebraicGeometry.IsRelativeEffectiveCartierDivisor
        (AlgebraicGeometry.RelativeEffectiveCartierCounterexample.morphism k)
        (AlgebraicGeometry.RelativeEffectiveCartierCounterexample.divisor k))

#check
  (AlgebraicGeometry.RelativeEffectiveCartierCounterexample.notFlat :
    ∀ (k : Type u) [Field k],
      ¬ Module.Flat
        (AlgebraicGeometry.RelativeEffectiveCartierCounterexample.Base k)
        (AlgebraicGeometry.RelativeEffectiveCartierCounterexample.Algebra k))

#check
  (AlgebraicGeometry.RelativeEffectiveCartierCounterexample.quotientToBase_bijective :
    ∀ (k : Type u) [Field k],
      Function.Bijective
        (AlgebraicGeometry.RelativeEffectiveCartierCounterexample.quotientToBase k))

#check
  (AlgebraicGeometry.RelativeEffectiveCartierCounterexample.quotient_flat :
    ∀ (k : Type u) [Field k],
      Module.Flat
        (AlgebraicGeometry.RelativeEffectiveCartierCounterexample.Base k)
        (AlgebraicGeometry.RelativeEffectiveCartierCounterexample.Quotient k))

#check
  (AlgebraicGeometry.RelativeEffectiveCartierCounterexample.x_mem_nonZeroDivisors :
    ∀ (k : Type u) [Field k],
      AlgebraicGeometry.RelativeEffectiveCartierCounterexample.x k ∈
        nonZeroDivisors
          (AlgebraicGeometry.RelativeEffectiveCartierCounterexample.Algebra k))

#check
  (AlgebraicGeometry.RelativeEffectiveCartierCounterexample.xSection_isRegular :
    ∀ (k : Type u) [Field k],
      AlgebraicGeometry.RingedSpace.IsRegularSection
        (SheafOfModules.unit
          (AlgebraicGeometry.RelativeEffectiveCartierCounterexample.scheme k).ringCatSheaf :
            (AlgebraicGeometry.RelativeEffectiveCartierCounterexample.scheme k).Modules)
        (AlgebraicGeometry.RelativeEffectiveCartierCounterexample.xSection k))

#check
  (AlgebraicGeometry.RelativeEffectiveCartierCounterexample.not_exists_flat_openContaining_support :
    ∀ (k : Type u) [Field k],
      ¬ ∃ U : (AlgebraicGeometry.RelativeEffectiveCartierCounterexample.scheme k).Opens,
        ((AlgebraicGeometry.RelativeEffectiveCartierCounterexample.divisor k).support :
            Set (AlgebraicGeometry.RelativeEffectiveCartierCounterexample.scheme k)) ⊆
          (U : Set (AlgebraicGeometry.RelativeEffectiveCartierCounterexample.scheme k)) ∧
          AlgebraicGeometry.Flat
            (U.ι ≫ AlgebraicGeometry.RelativeEffectiveCartierCounterexample.morphism k))

#check
  (AlgebraicGeometry.RelativeEffectiveCartierCounterexample.morphism_notFlat :
    ∀ (k : Type u) [Field k],
      ¬ AlgebraicGeometry.Flat
        (AlgebraicGeometry.RelativeEffectiveCartierCounterexample.morphism k))
