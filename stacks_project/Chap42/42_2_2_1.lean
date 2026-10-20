/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.Zero.Multiplicity
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

universe u v

variable {R : Type u} [Ring R]

/- 42.2.2.1: The Herbrand multiplicity of the two-periodic complex `(M, 0, ψ)` is
`length R (cokernel ψ) - length R (kernel ψ)`. -/
@[stacks 0EA6] #check
  (CategoryTheory.TwoPeriodicEndomorphism.multiplicity_ofZero :
    (M : ModuleCat.{v} R) → (ψ : M ⟶ M) →
      (hCoker : IsFiniteLength R (cokernel ψ : ModuleCat R)) →
      (hKer : IsFiniteLength R (kernel ψ : ModuleCat R)) →
      CategoryTheory.TwoPeriodicEndomorphism.multiplicity
          (CategoryTheory.TwoPeriodicEndomorphism.ofZero ψ)
          (CategoryTheory.TwoPeriodicEndomorphism.ofZero_homology_zero_isFiniteLength
            ψ hCoker)
          (CategoryTheory.TwoPeriodicEndomorphism.ofZero_homology_one_isFiniteLength
            ψ hKer) =
        ((Module.length R (cokernel ψ : ModuleCat R)).toNat : ℤ) -
          ((Module.length R (kernel ψ : ModuleCat R)).toNat : ℤ))
