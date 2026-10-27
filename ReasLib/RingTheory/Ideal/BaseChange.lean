/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Flat.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Flat base change of ideals

This file owns the canonical map from the scalar extension of an ideal to its mapped ideal. Under
flatness the map is bijective, so finite presentation passes to the mapped ideal.
-/

@[expose] public section

open scoped TensorProduct

noncomputable section

universe u v

namespace Ideal

variable {R : Type u} [CommRing R]
variable (I : Ideal R) (S : Type v) [CommRing S] [Algebra R S]

/-- The ambient multiplication map `S ⊗[R] I →ₗ[S] S` underlying extension of an ideal. -/
noncomputable def baseChangeMul : S ⊗[R] I →ₗ[S] S :=
  (TensorProduct.AlgebraTensorModule.rid R S S).toLinearMap.comp
    (((I : Submodule R R).baseChange S).subtype.comp
      ((I : Submodule R R).toBaseChange S))

/-- The ambient base-change multiplication map takes values in the mapped ideal. -/
theorem baseChangeMul_mem (x : S ⊗[R] I) :
    baseChangeMul I S x ∈ I.map (algebraMap R S) := by
  induction x using TensorProduct.induction_on with
  | zero => simpa using (I.map (algebraMap R S)).zero_mem
  | add x y hx hy => simpa only [map_add] using (I.map (algebraMap R S)).add_mem hx hy
  | tmul s x =>
    change (x : R) • s ∈ I.map (algebraMap R S)
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_right s _ (Ideal.mem_map_of_mem (algebraMap R S) x.property)

/-- The canonical linear map from the scalar extension of `I` to its extension as an ideal. -/
@[stacks 01BX "ideal base-change map"]
noncomputable def baseChangeMap : S ⊗[R] I →ₗ[S] I.map (algebraMap R S) :=
  (baseChangeMul I S).codRestrict (I.map (algebraMap R S)) (baseChangeMul_mem I S)

/-- The tensor unit identifies the scalar-extended ideal with its usual image ideal. -/
theorem map_baseChange_rid :
    ((I : Submodule R R).baseChange S).map
        (TensorProduct.AlgebraTensorModule.rid R S S).toLinearMap =
      (I.map (algebraMap R S) : Submodule S S) := by
  apply le_antisymm
  · rintro s ⟨t, ht, rfl⟩
    obtain ⟨x, hx⟩ := Submodule.toBaseChange_surjective' S (I : Submodule R R) ht
    have h := baseChangeMul_mem I S x
    change (TensorProduct.AlgebraTensorModule.rid R S S)
      (((I : Submodule R R).toBaseChange S) x : S ⊗[R] R) ∈ I.map (algebraMap R S) at h
    rwa [hx] at h
  · apply Ideal.map_le_iff_le_comap.mpr
    intro r hr
    refine ⟨1 ⊗ₜ[R] r, Submodule.tmul_mem_baseChange_of_mem (1 : S) hr, ?_⟩
    simp [Algebra.smul_def]

/-- Flat scalar extension identifies an ideal tensor product with the extended ideal.
Both directions use the canonical tensor range and the tensor unit equivalence. -/
noncomputable def baseChangeEquiv [Module.Flat R S] :
    S ⊗[R] I ≃ₗ[S] I.map (algebraMap R S) :=
  (Submodule.toBaseChange.toLinearEquiv S (I : Submodule R R)).trans
    (((TensorProduct.AlgebraTensorModule.rid R S S).submoduleMap
      ((I : Submodule R R).baseChange S)).trans
        (LinearEquiv.ofEq _ _ (map_baseChange_rid I S)))

/-- The flat ideal equivalence has the specified base-change multiplication map. -/
@[simp]
theorem baseChangeEquiv_toLinearMap [Module.Flat R S] :
    (baseChangeEquiv I S).toLinearMap = baseChangeMap I S := by
  ext x
  rfl

/-- The ideal base-change map sends a pure tensor to scalar multiplication of the mapped ideal
element. -/
@[simp]
theorem coe_baseChangeMap_tmul (s : S) (x : I) :
    (baseChangeMap I S (s ⊗ₜ[R] x) : S) = s * algebraMap R S x := by
  change (x : R) • s = s * algebraMap R S x
  rw [Algebra.smul_def, mul_comm]

/-- The ideal base-change map is always surjective. -/
theorem baseChangeMap_surjective : Function.Surjective (baseChangeMap I S) := by
  intro x
  have hx : (x : S) ∈ ((I : Submodule R R).baseChange S).map
      (TensorProduct.AlgebraTensorModule.rid R S S).toLinearMap := by
    rw [map_baseChange_rid]
    exact x.property
  obtain ⟨t, ht, htx⟩ := hx
  obtain ⟨z, hz⟩ := Submodule.toBaseChange_surjective' S (I : Submodule R R) ht
  refine ⟨z, ?_⟩
  apply Subtype.ext
  change (TensorProduct.AlgebraTensorModule.rid R S S)
    (((I : Submodule R R).toBaseChange S) z : S ⊗[R] R) = (x : S)
  rw [hz]
  exact htx

/-- Flatness makes the ideal base-change map injective. -/
theorem baseChangeMap_injective [Module.Flat R S] :
    Function.Injective (baseChangeMap I S) := by
  rw [← baseChangeEquiv_toLinearMap]
  exact (baseChangeEquiv I S).injective

/-- A finitely presented ideal remains finitely presented after mapping along a flat ring
homomorphism. -/
@[stacks 01BX "flat extension of finitely presented ideals"]
theorem finitePresentation_map_of_flat
    {T : Type v} [CommRing T] (I : Ideal R) (f : R →+* T) (hf : f.Flat)
    [Module.FinitePresentation R I] :
    Module.FinitePresentation T (I.map f) := sorry

end Ideal
