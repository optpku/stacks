/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.Rat.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Example 10.89.1

@stack 059I

Tensor products need not commute with infinite products, even for the flat `ℤ`-module `ℚ`.
-/

open scoped TensorProduct
open TensorProduct

/-- The canonical `ℤ`-linear map from `ℚ` to
`ℚ ⊗[ℤ] (∏ n : ℕ+, ZMod n)` induced by the residue maps `ℤ → ZMod n`. -/
noncomputable def rat_to_tensor_pnat_zmod_product :
    ℚ →ₗ[ℤ] ℚ ⊗[ℤ] ((n : ℕ+) → ZMod n) :=
  (TensorProduct.comm ℤ ((n : ℕ+) → ZMod n) ℚ).toLinearMap.comp
    ((LinearMap.rTensor ℚ (Algebra.linearMap ℤ ((n : ℕ+) → ZMod n))).comp
      (TensorProduct.lid ℤ ℚ).symm.toLinearMap)

/-- A rational sequence has a common nonzero integer denominator when all its terms can be
written as `a n / m` for a single nonzero `m : ℤ`. -/
def has_common_integer_denominator (x : ℕ+ → ℚ) : Prop :=
  ∃ a : ℕ+ → ℤ, ∃ m : ℤ, m ≠ 0 ∧ ∀ n : ℕ+, x n = (a n : ℚ) / m

/-- Example 10.89.1 (1): for `Q n = ZMod n`, the product
`∏ n : ℕ+, ℚ ⊗[ℤ] Q n` is the zero module. -/
@[stacks 059I "(1), the product of the componentwise tensor products vanishes"]
theorem rat_tensor_pnat_zmod_product_subsingleton :
    Subsingleton ((n : ℕ+) → ℚ ⊗[ℤ] ZMod n) := sorry

/-- Example 10.89.1 (2): tensoring the injective residue map
`ℤ → ∏ n : ℕ+, ZMod n` with `ℚ` gives an injective map into the tensor product. -/
@[stacks 059I "(2), the tensor product of the product is nonzero"]
theorem rat_to_tensor_pnat_zmod_product_injective :
    Function.Injective rat_to_tensor_pnat_zmod_product := sorry

/-- Example 10.89.1 (3): the canonical map from the tensor product of the `ZMod n` product to
the product of the componentwise tensor products is not injective. -/
@[stacks 059I "(3), the tensor-product-to-product map is not injective"]
theorem rat_tensor_pnat_zmod_product_map_not_injective :
    ¬ Function.Injective (piRightHom ℤ ℤ ℚ (fun n : ℕ+ ↦ ZMod n)) := sorry

/-- Example 10.89.1 (4): a rational sequence belongs to the image of
`ℚ ⊗[ℤ] (∏ n : ℕ+, ℤ) → ∏ n : ℕ+, ℚ` exactly when it has a common nonzero integer denominator. -/
@[stacks 059I "(4), range of the tensor-product-to-product map"]
theorem mem_rat_tensor_pnat_int_product_map_range_iff_has_common_integer_denominator
    (x : ℕ+ → ℚ) :
    x ∈ LinearMap.range (piScalarRightHom ℤ ℤ ℚ ℕ+) ↔ has_common_integer_denominator x := sorry

/-- Example 10.89.1 (5): the canonical map
`ℚ ⊗[ℤ] (∏ n : ℕ+, ℤ) → ∏ n : ℕ+, ℚ` is not surjective. -/
@[stacks 059I "(5), the tensor-product-to-product map is not surjective"]
theorem rat_tensor_pnat_int_product_map_not_surjective :
    ¬ Function.Surjective (piScalarRightHom ℤ ℤ ℚ ℕ+) := sorry

#check @TensorProduct.piRightHom
#check @TensorProduct.piScalarRightHom
