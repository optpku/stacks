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

/-- Every one-variable divided-power polynomial has a finite coefficient expansion. -/
theorem ofSupport_surjective :
    Function.Surjective (ofSupport : (ℕ →₀ B) →ₗ[B] Ring B 1) := by
  intro f
  induction f using DividedPowerAlgebra.induction_on with
  | C b =>
    exact ⟨Finsupp.single 0 b, by
      simp [ofSupport, DPPolynomial.dp, DividedPowerAlgebra.dp_zero, Algebra.smul_def]⟩
  | add f g hf hg =>
    obtain ⟨l, rfl⟩ := hf
    obtain ⟨k, rfl⟩ := hg
    exact ⟨l + k, map_add _ _ _⟩
  | dp f n v hf =>
    obtain ⟨l, rfl⟩ := hf
    have hv : v = v 0 • Finsupp.single (0 : Fin 1) (1 : B) := by
      have h0 : (default : Fin 1) = 0 := Subsingleton.elim _ _
      simpa only [h0, Finsupp.smul_single, smul_eq_mul, mul_one] using Finsupp.unique_single v
    rw [hv, DividedPowerAlgebra.dp_smul]
    change ∃ k, ofSupport k = ofSupport l * ((v 0) ^ n • DPPolynomial.dp B n (0 : Fin 1))
    induction l using Finsupp.induction_linear with
    | zero => exact ⟨0, by simp⟩
    | add l₁ l₂ h₁ h₂ =>
      obtain ⟨k₁, hk₁⟩ := h₁
      obtain ⟨k₂, hk₂⟩ := h₂
      exact ⟨k₁ + k₂, by simp only [map_add, add_mul, hk₁, hk₂]⟩
    | single m b =>
      refine ⟨Finsupp.single (m + n) ((m + n).choose m • (b * (v 0) ^ n)), ?_⟩
      simp only [ofSupport, Finsupp.linearCombination_single]
      rw [smul_mul_smul_comm, DividedPowerAlgebra.dp_mul]
      simpa only [smul_assoc] using
        smul_comm ((m + n).choose m) (b * (v 0) ^ n)
          (DPPolynomial.dp B (m + n) (0 : Fin 1))

/-- The family `m ↦ dp m 0` is a `B`-basis of `Finite.Ring B 1`. -/
theorem ofSupport_bijective :
    Function.Bijective (ofSupport : (ℕ →₀ B) →ₗ[B] Ring B 1) := by
  refine ⟨?_, ofSupport_surjective⟩
  -- Linear independence of the formal divided-power monomials over an arbitrary base ring.
  sorry

/-- Coefficient expansion of one-variable divided-power polynomials against `dp m 0`. -/
noncomputable def supportEquiv : (ℕ →₀ B) ≃ₗ[B] Ring B 1 where
  toFun := ofSupport
  invFun := Function.invFun ofSupport
  left_inv := Function.leftInverse_invFun ofSupport_bijective.1
  right_inv := Function.rightInverse_invFun ofSupport_bijective.2
  map_add' := ofSupport.map_add
  map_smul' := ofSupport.map_smul

private theorem supportEquiv_symm_ofSupport (l : ℕ →₀ B) :
    supportEquiv.symm (ofSupport l) = l :=
  supportEquiv.symm_apply_apply l

private theorem supportEquiv_symm_dp (m : ℕ) :
    supportEquiv.symm (DPPolynomial.dp B m (0 : Fin 1)) = Finsupp.single m 1 := by
  apply supportEquiv.injective
  rw [LinearEquiv.apply_symm_apply]
  change DPPolynomial.dp B m (0 : Fin 1) = ofSupport (Finsupp.single m 1)
  simp [ofSupport]

private theorem supportEquiv_symm_algebraMap (b : B) :
    supportEquiv.symm (algebraMap B (Ring B 1) b) = Finsupp.single 0 b := by
  apply supportEquiv.injective
  rw [LinearEquiv.apply_symm_apply]
  change algebraMap B (Ring B 1) b = ofSupport (Finsupp.single 0 b)
  simp [ofSupport, DPPolynomial.dp, DividedPowerAlgebra.dp_zero, Algebra.smul_def]

/-- The `B`-linear degree-shift `θ` sending `dp m 0` to `dp (m + 1) 0`. -/
noncomputable def shift : Ring B 1 →ₗ[B] Ring B 1 :=
  ofSupport.comp ((Finsupp.lmapDomain B B Nat.succ).comp supportEquiv.symm.toLinearMap)

/-- The `B`-linear operator `∂_z` sending `dp (m + 1) 0` to `dp m 0` and constants to `0`. -/
noncomputable def partialZ : Ring B 1 →ₗ[B] Ring B 1 :=
  ofSupport.comp
    ((Finsupp.lcomapDomain Nat.succ Nat.succ_injective).comp supportEquiv.symm.toLinearMap)

/-- The constant coefficient of a one-variable divided-power polynomial. -/
theorem constantTerm_map_one :
    supportEquiv.symm (1 : Ring B 1) 0 = 1 := by
  simpa using congrArg (fun l : ℕ →₀ B ↦ l 0) (supportEquiv_symm_algebraMap (1 : B))

/-- The constant coefficient is multiplicative. -/
theorem constantTerm_map_mul (f g : Ring B 1) :
    supportEquiv.symm (f * g) 0 =
      supportEquiv.symm f 0 * supportEquiv.symm g 0 := by
  obtain ⟨l, rfl⟩ := supportEquiv.surjective f
  obtain ⟨k, rfl⟩ := supportEquiv.surjective g
  induction l using Finsupp.induction_linear with
  | zero => simp
  | add l₁ l₂ h₁ h₂ => simp_all [add_mul]
  | single m b =>
    induction k using Finsupp.induction_linear with
    | zero => simp
    | add k₁ k₂ h₁ h₂ => simp_all [mul_add]
    | single n c =>
      change supportEquiv.symm (ofSupport (Finsupp.single m b) *
          ofSupport (Finsupp.single n c)) 0 =
        supportEquiv.symm (ofSupport (Finsupp.single m b)) 0 *
          supportEquiv.symm (ofSupport (Finsupp.single n c)) 0
      simp only [ofSupport, Finsupp.linearCombination_single, smul_mul_smul_comm]
      rw [show DPPolynomial.dp B m (0 : Fin 1) * DPPolynomial.dp B n (0 : Fin 1) =
        (m + n).choose m • DPPolynomial.dp B (m + n) (0 : Fin 1) from
          DividedPowerAlgebra.dp_mul]
      simp only [map_smul, map_nsmul, Finsupp.smul_apply,
        supportEquiv_symm_dp]
      cases m <;> cases n <;> simp

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
      DPPolynomial.dp B (m + 1) (0 : Fin 1) := by
  simp [shift, supportEquiv_symm_dp, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single, ofSupport]

/-- The scalar-weighted shift of a divided-power monomial. -/
theorem shift_smul_dp (b : B) (m : ℕ) :
    shift (algebraMap B (Ring B 1) b * DPPolynomial.dp B m (0 : Fin 1)) =
      algebraMap B (Ring B 1) b * DPPolynomial.dp B (m + 1) (0 : Fin 1) := by
  simpa only [Algebra.smul_def, shift_dp] using
    (shift : Ring B 1 →ₗ[B] Ring B 1).map_smul b (DPPolynomial.dp B m (0 : Fin 1))

/-- `θ` acts on constants by multiplication by the generator `X 0`. -/
theorem shift_algebraMap (b : B) :
    shift (algebraMap B (Ring B 1) b) =
      algebraMap B (Ring B 1) b * DPPolynomial.X B (0 : Fin 1) := by
  have h := shift_smul_dp b 0
  simpa only [DPPolynomial.dp, DividedPowerAlgebra.dp_zero, mul_one, DPPolynomial.X,
    DividedPowerAlgebra.embed_def, Nat.zero_add] using h

/-- `∂_z` annihilates constants. -/
theorem partialZ_algebraMap (b : B) : partialZ (algebraMap B (Ring B 1) b) = 0 := by
  simp [partialZ, supportEquiv_symm_algebraMap, Finsupp.lcomapDomain,
    Finsupp.comapDomain_single_of_not_mem_range (by simp : 0 ∉ Set.range Nat.succ)]

/-- `∂_z` lowers the divided-power degree of a positive generator by one. -/
theorem partialZ_dp (m : ℕ) :
    partialZ (DPPolynomial.dp B (m + 1) (0 : Fin 1)) =
      DPPolynomial.dp B m (0 : Fin 1) := by
  simp [partialZ, supportEquiv_symm_dp, Finsupp.lcomapDomain,
    Finsupp.comapDomain_single, ofSupport]

/-- In the `a = 1` case, `∂_z ∘ θ` is the identity. -/
theorem partialZ_comp_shift (f : Ring B 1) : partialZ (shift f) = f := by
  simp only [partialZ, shift, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    supportEquiv_symm_ofSupport, Finsupp.lmapDomain_apply]
  rw [Finsupp.leftInverse_lcomapDomain_mapDomain Nat.succ Nat.succ_injective]
  exact supportEquiv.apply_symm_apply f

/-- Constant term of a scalar. -/
theorem constantTerm_algebraMap (b : B) : constantTerm (algebraMap B (Ring B 1) b) = b := by
  change supportEquiv.symm (algebraMap B (Ring B 1) b) 0 = b
  simp [supportEquiv_symm_algebraMap]

/-- Positive divided-power monomials have vanishing constant term. -/
theorem constantTerm_dp (m : ℕ) :
    constantTerm (DPPolynomial.dp B (m + 1) (0 : Fin 1)) = 0 := by
  change supportEquiv.symm (DPPolynomial.dp B (m + 1) (0 : Fin 1)) 0 = 0
  simp [supportEquiv_symm_dp]

/-- The identity `f - θ(∂_z f) = f(0)` in `Finite.Ring B 1`. -/
theorem sub_shift_partialZ (f : Ring B 1) :
    f - shift (partialZ f) = algebraMap B (Ring B 1) (constantTerm f) := by
  apply supportEquiv.symm.injective
  ext n
  simp only [map_sub, Finsupp.sub_apply, supportEquiv_symm_algebraMap]
  simp only [shift, partialZ, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    supportEquiv_symm_ofSupport, Finsupp.lmapDomain_apply]
  cases n with
  | zero =>
    rw [Finsupp.mapDomain_notin_range _ _ (by simp : 0 ∉ Set.range Nat.succ)]
    simp [constantTerm]
  | succ n =>
    rw [Finsupp.mapDomain_apply Nat.succ_injective]
    simp [Finsupp.lcomapDomain]

end DPPolynomial.Finite
