/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.Submodule.EqLocus
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

universe u

open LinearMap
open scoped TensorProduct

namespace TensorProduct

variable (A : Type u) {I : Type u} (A_ : I → Type u)
  [CommRing A] [∀ i, CommRing (A_ i)] [∀ i, Algebra A (A_ i)]
variable (M : Type u) [AddCommGroup M] [Module A M]

/-- The canonical `A`-linear map `M → ∏ i, M ⊗[A] A_ i` sending `m` to the family
`i ↦ m ⊗ₜ 1`. -/
def piUnit : M →ₗ[A] ((i : I) → M ⊗[A] A_ i) :=
  pi fun i ↦ (mk A M (A_ i)).flip 1

/-- The left parallel arrow `∏ i, M ⊗[A] A_ i → ∏ p, M ⊗[A] (A_ p.1 ⊗[A] A_ p.2)` whose
`(i, j)`-component is `lTensor M includeLeft` after projection to the `i`-factor. -/
def piIncludeLeft :
    ((i : I) → M ⊗[A] A_ i) →ₗ[A] ((p : I × I) → M ⊗[A] (A_ p.1 ⊗[A] A_ p.2)) :=
  pi fun p ↦
    lTensor M (Algebra.TensorProduct.includeLeft : A_ p.1 →ₐ[A] A_ p.1 ⊗[A] A_ p.2).toLinearMap ∘ₗ
      proj p.1

/-- The right parallel arrow `∏ i, M ⊗[A] A_ i → ∏ p, M ⊗[A] (A_ p.1 ⊗[A] A_ p.2)` whose
`(i, j)`-component is `lTensor M includeRight` after projection to the `j`-factor. -/
def piIncludeRight :
    ((i : I) → M ⊗[A] A_ i) →ₗ[A] ((p : I × I) → M ⊗[A] (A_ p.1 ⊗[A] A_ p.2)) :=
  pi fun p ↦
    lTensor M (Algebra.TensorProduct.includeRight : A_ p.2 →ₐ[A] A_ p.1 ⊗[A] A_ p.2).toLinearMap ∘ₗ
      proj p.2

/-- The `i`-component of `piUnit` is `m ⊗ₜ 1`. -/
theorem piUnit_apply (m : M) (i : I) : piUnit A A_ M m i = m ⊗ₜ 1 := sorry

/-- The `(i, j)`-component of `piIncludeLeft` is `lTensor M includeLeft` on the `i`-factor. -/
theorem piIncludeLeft_apply (x : (i : I) → M ⊗[A] A_ i) (i j : I) :
    piIncludeLeft A A_ M x (i, j) =
      lTensor M (Algebra.TensorProduct.includeLeft : A_ i →ₐ[A] A_ i ⊗[A] A_ j).toLinearMap
        (x i) := sorry

/-- The `(i, j)`-component of `piIncludeRight` is `lTensor M includeRight` on the `j`-factor. -/
theorem piIncludeRight_apply (x : (i : I) → M ⊗[A] A_ i) (i j : I) :
    piIncludeRight A A_ M x (i, j) =
      lTensor M (Algebra.TensorProduct.includeRight : A_ j →ₐ[A] A_ i ⊗[A] A_ j).toLinearMap
        (x j) := sorry

/-- The two Čech cofaces agree after composition with the canonical unit. -/
theorem piIncludeLeft_comp_piUnit :
    piIncludeLeft A A_ M ∘ₗ piUnit A A_ M = piIncludeRight A A_ M ∘ₗ piUnit A A_ M := sorry

end TensorProduct

namespace Module

open TensorProduct

variable (A : Type u) {I : Type u} (A_ : I → Type u)
  [CommRing A] [∀ i, CommRing (A_ i)] [∀ i, Algebra A (A_ i)]
variable (M : Type u) [AddCommGroup M] [Module A M]

/-- An `A`-module `M` is the equalizer of `piIncludeLeft` and `piIncludeRight` if the canonical
unit `piUnit A A_ M` is injective and its range is the equalizer locus of those two maps. -/
def IsPiTensorEqualizer : Prop :=
  Function.Injective (piUnit A A_ M) ∧
    LinearMap.range (piUnit A A_ M) =
      LinearMap.eqLocus (piIncludeLeft A A_ M) (piIncludeRight A A_ M)

/-- `IsPiTensorEqualizer` unfolds as injectivity of `piUnit` together with the range-equalizer
identification. -/
theorem isPiTensorEqualizer_iff :
    IsPiTensorEqualizer A A_ M ↔
      Function.Injective (piUnit A A_ M) ∧
        LinearMap.range (piUnit A A_ M) =
          LinearMap.eqLocus (piIncludeLeft A A_ M) (piIncludeRight A A_ M) := sorry

end Module
