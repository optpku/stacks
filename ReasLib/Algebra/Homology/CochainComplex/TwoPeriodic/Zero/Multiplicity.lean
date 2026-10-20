/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.Zero
public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.Multiplicity

/-!
# Multiplicity of Zero-First-Differential Two-Periodic Complexes

This file identifies the finite homology and multiplicity of a two-periodic endomorphism
complex whose first differential is zero.
-/

@[expose] public section

open CategoryTheory Limits

universe u v

namespace CategoryTheory.TwoPeriodicEndomorphism

variable {R : Type u} [Ring R] {M : ModuleCat.{v} R}

/-- Finite length of the cokernel of `ψ` gives finite degree-zero homology for `ofZero ψ`. -/
theorem ofZero_homology_zero_isFiniteLength (ψ : M ⟶ M)
    (hCoker : IsFiniteLength R (cokernel ψ : ModuleCat R)) :
    IsFiniteLength R ((ofZero ψ).toCochainComplex.homology 0) := sorry

/-- Finite length of the kernel of `ψ` gives finite degree-one homology for `ofZero ψ`. -/
theorem ofZero_homology_one_isFiniteLength (ψ : M ⟶ M)
    (hKer : IsFiniteLength R (kernel ψ : ModuleCat R)) :
    IsFiniteLength R ((ofZero ψ).toCochainComplex.homology 1) := sorry

/-- The multiplicity of the zero-first-differential two-periodic complex is the length of the
cokernel of its second differential minus the length of its kernel. -/
@[stacks 0EA6]
theorem multiplicity_ofZero (M : ModuleCat.{v} R) (ψ : M ⟶ M)
    (hCoker : IsFiniteLength R (cokernel ψ : ModuleCat R))
    (hKer : IsFiniteLength R (kernel ψ : ModuleCat R)) :
    multiplicity (ofZero ψ) (ofZero_homology_zero_isFiniteLength ψ hCoker)
        (ofZero_homology_one_isFiniteLength ψ hKer) =
      ((Module.length R (cokernel ψ : ModuleCat R)).toNat : ℤ) -
        ((Module.length R (kernel ψ : ModuleCat R)).toNat : ℤ) := sorry

end CategoryTheory.TwoPeriodicEndomorphism
