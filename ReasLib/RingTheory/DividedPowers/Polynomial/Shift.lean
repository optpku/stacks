/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.Finsupp.Defs
public import ReasLib.RingTheory.DividedPowers.Polynomial

@[expose] public section

universe u

namespace DPPolynomial.Finite

variable {B : Type u} [CommRing B]

/-- Expansion of a finitely supported family of coefficients as a linear combination of
the one-variable divided-power monomials `dp m 0`. -/
noncomputable def ofSupport : (ℕ →₀ B) →ₗ[B] Ring B 1 :=
  Finsupp.linearCombination B fun m ↦ DPPolynomial.dp B m (0 : Fin 1)

/-- The family `m ↦ dp m 0` is a `B`-basis of `Finite.Ring B 1`. -/
theorem ofSupport_bijective :
    Function.Bijective (ofSupport : (ℕ →₀ B) →ₗ[B] Ring B 1) := sorry

/-- Coefficient expansion of one-variable divided-power polynomials against `dp m 0`. -/
noncomputable def supportEquiv : (ℕ →₀ B) ≃ₗ[B] Ring B 1 where
  toFun := ofSupport
  invFun := Function.invFun ofSupport
  left_inv := Function.leftInverse_invFun ofSupport_bijective.1
  right_inv := Function.rightInverse_invFun ofSupport_bijective.2
  map_add' := ofSupport.map_add
  map_smul' := ofSupport.map_smul

/-- The `B`-linear degree-shift `θ` sending `dp m 0` to `dp (m + 1) 0`. -/
noncomputable def shift : Ring B 1 →ₗ[B] Ring B 1 :=
  ofSupport.comp ((Finsupp.lmapDomain B B Nat.succ).comp supportEquiv.symm.toLinearMap)

/-- The `B`-linear operator `∂_z` sending `dp (m + 1) 0` to `dp m 0` and constants to `0`. -/
noncomputable def partialZ : Ring B 1 →ₗ[B] Ring B 1 :=
  ofSupport.comp
    ((Finsupp.lcomapDomain Nat.succ Nat.succ_injective).comp supportEquiv.symm.toLinearMap)

/-- The constant coefficient of a one-variable divided-power polynomial. -/
theorem constantTerm_map_one :
    supportEquiv.symm (1 : Ring B 1) 0 = 1 := sorry

/-- The constant coefficient is multiplicative. -/
theorem constantTerm_map_mul (f g : Ring B 1) :
    supportEquiv.symm (f * g) 0 =
      supportEquiv.symm f 0 * supportEquiv.symm g 0 := sorry

/-- The constant-term retraction `f ↦ f(0)` of `algebraMap B (Finite.Ring B 1)`. -/
noncomputable def constantTerm : Ring B 1 →+* B where
  toFun f := supportEquiv.symm f 0
  map_one' := constantTerm_map_one
  map_mul' := constantTerm_map_mul
  map_zero' := by simp
  map_add' := by simp

/-- `θ` raises the divided-power degree of a generator by one. -/
theorem shift_dp (m : ℕ) :
    shift (DPPolynomial.dp B m (0 : Fin 1)) =
      DPPolynomial.dp B (m + 1) (0 : Fin 1) := sorry

/-- The scalar-weighted shift of a divided-power monomial. -/
theorem shift_smul_dp (b : B) (m : ℕ) :
    shift (algebraMap B (Ring B 1) b * DPPolynomial.dp B m (0 : Fin 1)) =
      algebraMap B (Ring B 1) b * DPPolynomial.dp B (m + 1) (0 : Fin 1) := sorry

/-- `θ` acts on constants by multiplication by the generator `X 0`. -/
theorem shift_algebraMap (b : B) :
    shift (algebraMap B (Ring B 1) b) =
      algebraMap B (Ring B 1) b * DPPolynomial.X B (0 : Fin 1) := sorry

/-- `∂_z` annihilates constants. -/
theorem partialZ_algebraMap (b : B) : partialZ (algebraMap B (Ring B 1) b) = 0 := sorry

/-- `∂_z` lowers the divided-power degree of a positive generator by one. -/
theorem partialZ_dp (m : ℕ) :
    partialZ (DPPolynomial.dp B (m + 1) (0 : Fin 1)) =
      DPPolynomial.dp B m (0 : Fin 1) := sorry

/-- In the `a = 1` case, `∂_z ∘ θ` is the identity. -/
theorem partialZ_comp_shift (f : Ring B 1) : partialZ (shift f) = f := sorry

/-- Constant term of a scalar. -/
theorem constantTerm_algebraMap (b : B) : constantTerm (algebraMap B (Ring B 1) b) = b := sorry

/-- Positive divided-power monomials have vanishing constant term. -/
theorem constantTerm_dp (m : ℕ) :
    constantTerm (DPPolynomial.dp B (m + 1) (0 : Fin 1)) = 0 := sorry

/-- The identity `f - θ(∂_z f) = f(0)` in `Finite.Ring B 1`. -/
theorem sub_shift_partialZ (f : Ring B 1) :
    f - shift (partialZ f) = algebraMap B (Ring B 1) (constantTerm f) := sorry

end DPPolynomial.Finite
