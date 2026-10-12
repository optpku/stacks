/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.TensorAlgebra.ToTensorPower
public import Mathlib.RingTheory.TwoSidedIdeal.Operations

@[expose] public section

open scoped TensorProduct

universe u

namespace MilnorK

/-- The Steinberg generators in the tensor algebra on the additive form of `kˣ`.
Writing the two units as `x` and `y` with `x + y = 1` avoids making a proof-valued
choice of a unit structure on `1 - x`. -/
def steinbergGenerators (k : Type u) [Field k] :
    Set (TensorAlgebra ℤ (Additive kˣ)) :=
  {z | ∃ x y : kˣ, (x : k) + (y : k) = 1 ∧
    z = TensorAlgebra.ι ℤ (Additive.ofMul x) *
      TensorAlgebra.ι ℤ (Additive.ofMul y)}

/-- Membership in the set of Steinberg generators is the unit-pair relation `x + y = 1`. -/
theorem mem_steinbergGenerators_iff {k : Type u} [Field k]
    {z : TensorAlgebra ℤ (Additive kˣ)} :
    z ∈ steinbergGenerators k ↔ ∃ x y : kˣ, (x : k) + (y : k) = 1 ∧
      z = TensorAlgebra.ι ℤ (Additive.ofMul x) *
        TensorAlgebra.ι ℤ (Additive.ofMul y) := sorry

/-- The two-sided Steinberg ideal in the tensor algebra on `Additive kˣ`. -/
def steinbergIdeal (k : Type u) [Field k] :
    TwoSidedIdeal (TensorAlgebra ℤ (Additive kˣ)) :=
  TwoSidedIdeal.span (steinbergGenerators k)

/-- Every Steinberg generator belongs to the Steinberg ideal. -/
theorem mem_steinbergIdeal_of_mem_generators {k : Type u} [Field k]
    {z : TensorAlgebra ℤ (Additive kˣ)} (hz : z ∈ steinbergGenerators k) :
    z ∈ steinbergIdeal k := sorry

/-- The graded Milnor K-ring of a field, presented as the tensor algebra on `kˣ`
modulo the two-sided Steinberg ideal. -/
abbrev Ring (k : Type u) [Field k] := (steinbergIdeal k).ringCon.Quotient

/-- The canonical quotient map from the tensor algebra to the Milnor K-ring. -/
def quotientMk (k : Type u) [Field k] :
    TensorAlgebra ℤ (Additive kˣ) →+* Ring k :=
  (steinbergIdeal k).ringCon.mk'

/-- The canonical map onto the Milnor K-ring is surjective. -/
theorem quotientMk_surjective (k : Type u) [Field k] :
    Function.Surjective (quotientMk k) := sorry

/-- A Steinberg generator maps to zero in the Milnor K-ring. -/
theorem quotientMk_steinberg {k : Type u} [Field k]
    (x y : kˣ) (hxy : (x : k) + (y : k) = 1) :
    quotientMk k
      (TensorAlgebra.ι ℤ (Additive.ofMul x) * TensorAlgebra.ι ℤ (Additive.ofMul y)) = 0 := sorry

/-- The degree-`n` part of the Milnor K-ring, as the image of the `n`th tensor power. -/
def degree (n : ℕ) (k : Type u) [Field k] : Submodule ℤ (Ring k) :=
  LinearMap.range ((quotientMk k).toIntAlgHom.toLinearMap.comp
    (TensorPower.toTensorAlgebra :
      (⨂[ℤ]^n (Additive kˣ)) →ₗ[ℤ] TensorAlgebra ℤ (Additive kˣ)))

/-- The degree-`n` Milnor K-group of `k`. -/
abbrev Group (n : ℕ) (k : Type u) [Field k] := degree n k

/-- The degree submodule is the image of the canonical map from the corresponding tensor power. -/
theorem degree_eq_range (n : ℕ) (k : Type u) [Field k] :
    degree n k = LinearMap.range ((quotientMk k).toIntAlgHom.toLinearMap.comp
      (TensorPower.toTensorAlgebra :
        (⨂[ℤ]^n (Additive kˣ)) →ₗ[ℤ] TensorAlgebra ℤ (Additive kˣ))) := sorry

/-- A pure tensor maps into the degree-`n` part of the Milnor K-ring. -/
theorem pureSymbol_mem_degree {n : ℕ} {k : Type u} [Field k] (x : Fin n → kˣ) :
    quotientMk k (TensorAlgebra.tprod ℤ (Additive kˣ) n (fun i ↦ Additive.ofMul (x i))) ∈
      degree n k := sorry

/-- The pure Milnor symbol associated to an `n`-tuple of units. -/
def symbol {n : ℕ} {k : Type u} [Field k] (x : Fin n → kˣ) : Group n k :=
  ⟨quotientMk k (TensorAlgebra.tprod ℤ (Additive kˣ) n (fun i ↦ Additive.ofMul (x i))),
    pureSymbol_mem_degree x⟩

/-- The underlying ring element of a pure Milnor symbol is the image of its pure tensor. -/
theorem symbol_coe {n : ℕ} {k : Type u} [Field k] (x : Fin n → kˣ) :
    (symbol x : Ring k) =
      quotientMk k (TensorAlgebra.tprod ℤ (Additive kˣ) n (fun i ↦ Additive.ofMul (x i))) := sorry

end MilnorK
