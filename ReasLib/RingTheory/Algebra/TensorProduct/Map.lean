/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor-product maps

This leaf collects reusable inverse and surjectivity criteria for changing one
factor of an algebra tensor product. It complements Mathlib's `rTensor`,
`productMap`, and `map_comp` API without fixing a presentation or a source
chapter.

@stack 05N8
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u v w x

namespace Algebra.TensorProduct

variable {R : Type u} {B : Type v} {C : Type w} {T : Type x}
variable [CommSemiring R] [CommSemiring B] [CommSemiring C] [CommSemiring T]
variable [Algebra R B] [Algebra R C] [Algebra R T]

/-- If `v` is a right inverse to `u` on the left tensor factor, its product
with the right inclusion is a right inverse to `rTensor T u`. -/
@[stacks 05N8 "tensor base-change right inverse"]
theorem rTensor_comp_productMap_eq_id
    (u : B →ₐ[R] C) (v : C →ₐ[R] B ⊗[R] T)
    (h : (rTensor (R := R) T u).comp v = includeLeft) :
    (rTensor (R := R) T u).comp (productMap v includeRight) = AlgHom.id R _ := sorry

/-- If `v` is a left inverse to `u` on the left tensor factor, its product
with the right inclusion is a left inverse to `rTensor T u`. -/
@[stacks 05N8 "tensor base-change left inverse"]
theorem productMap_comp_rTensor_eq_id
    (u : B →ₐ[R] C) (v : C →ₐ[R] B ⊗[R] T)
    (h : v.comp u = includeLeft) :
    (productMap v includeRight).comp (rTensor (R := R) T u) = AlgHom.id R _ := sorry

/-- An inverse on the left tensor factor, compatible with the right factor,
induces an algebra equivalence after tensoring. -/
@[stacks 05N8 "tensor base-change equivalence"]
noncomputable def rTensorEquivOfInverse
    (u : B →ₐ[R] C) (v : C →ₐ[R] B ⊗[R] T)
    (hvu : v.comp u = includeLeft)
    (huv : (rTensor (R := R) T u).comp v = includeLeft) :
    B ⊗[R] T ≃ₐ[R] C ⊗[R] T :=
  AlgEquiv.ofAlgHom (rTensor (R := R) T u) (productMap v includeRight)
    (rTensor_comp_productMap_eq_id u v huv)
    (productMap_comp_rTensor_eq_id u v hvu)

/-- The forward algebra homomorphism of `rTensorEquivOfInverse` is the
canonical right tensor map. -/
@[simp, stacks 05N8 "tensor base-change equivalence forward map"]
theorem rTensorEquivOfInverse_toAlgHom
    (u : B →ₐ[R] C) (v : C →ₐ[R] B ⊗[R] T)
    (hvu : v.comp u = includeLeft)
    (huv : (rTensor (R := R) T u).comp v = includeLeft) :
    (rTensorEquivOfInverse u v hvu huv).toAlgHom = rTensor (R := R) T u := sorry

/-- The inverse algebra homomorphism of `rTensorEquivOfInverse` is the
product map assembled from `v` and the right inclusion. -/
@[simp, stacks 05N8 "tensor base-change equivalence inverse map"]
theorem rTensorEquivOfInverse_symm_toAlgHom
    (u : B →ₐ[R] C) (v : C →ₐ[R] B ⊗[R] T)
    (hvu : v.comp u = includeLeft)
    (huv : (rTensor (R := R) T u).comp v = includeLeft) :
    (rTensorEquivOfInverse u v hvu huv).symm.toAlgHom =
      productMap v includeRight := sorry

/-- A right tensor map is surjective when a generating set for its target
left factor has prescribed preimages. The generation hypothesis explicitly
includes the image of the original left-factor map, avoiding a map-dependent
`Algebra B C` instance. -/
@[stacks 05N8 "tensor base-change surjectivity"]
theorem rTensor_surjective_of_generator_preimages
    (u : B →ₐ[R] C) (s : Set C)
    (hs : Algebra.adjoin R (Set.range u ∪ s) = ⊤)
    (hpre : ∀ x ∈ s, ∃ y : B ⊗[R] T,
      rTensor (R := R) T u y = (x ⊗ₜ[R] (1 : T) : C ⊗[R] T)) :
    Function.Surjective (rTensor (R := R) T u) := sorry

end Algebra.TensorProduct
