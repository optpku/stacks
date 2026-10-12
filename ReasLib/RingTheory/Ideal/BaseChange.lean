/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.RingHom.Flat
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
    baseChangeMul I S x ∈ I.map (algebraMap R S) := sorry

/-- The canonical linear map from the scalar extension of `I` to its extension as an ideal. -/
@[stacks 01BX "ideal base-change map"]
noncomputable def baseChangeMap : S ⊗[R] I →ₗ[S] I.map (algebraMap R S) :=
  (baseChangeMul I S).codRestrict (I.map (algebraMap R S)) (baseChangeMul_mem I S)

/-- The ideal base-change map sends a pure tensor to scalar multiplication of the mapped ideal
element. -/
@[simp]
theorem coe_baseChangeMap_tmul (s : S) (x : I) :
    (baseChangeMap I S (s ⊗ₜ[R] x) : S) = s * algebraMap R S x := sorry

/-- The ideal base-change map is always surjective. -/
theorem baseChangeMap_surjective : Function.Surjective (baseChangeMap I S) := sorry

/-- Flatness makes the ideal base-change map injective. -/
theorem baseChangeMap_injective [Module.Flat R S] :
    Function.Injective (baseChangeMap I S) := sorry

/-- A finitely presented ideal remains finitely presented after mapping along a flat ring
homomorphism. -/
@[stacks 01BX "flat extension of finitely presented ideals"]
theorem finitePresentation_map_of_flat
    {T : Type v} [CommRing T] (I : Ideal R) (f : R →+* T) (hf : f.Flat)
    [Module.FinitePresentation R I] :
    Module.FinitePresentation T (I.map f) := sorry

end Ideal
