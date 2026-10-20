module

public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra

/-!
# Tensor Base Change

This leaf provides canonical comparison maps for tensor products under a change
of scalars. The right tensor-factor algebra structure is enabled only inside
this module, so clients receive a concrete ring equivalence without a new global
instance.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct Algebra.TensorProduct.Right

universe u v w x

namespace Algebra.TensorProduct

/-- After changing the base from `k` to `k'`, the iterated tensor product
`(K ⊗[k] k') ⊗[k'] A` has the same underlying ring as `K ⊗[k] A`. This is the
right-oriented composite of Mathlib's tensor commutors and `cancelBaseChange`. -/
@[stacks 0C2Y "tensor base-change coherence"]
noncomputable def baseChangeRight
    {k : Type u} {k' : Type v} {K : Type w} {A : Type x}
    [CommRing k] [CommRing k'] [CommRing K] [CommRing A]
    [Algebra k k'] [Algebra k K] [Algebra k' A] [Algebra k A] [IsScalarTower k k' A] :
    (K ⊗[k] k') ⊗[k'] A ≃+* K ⊗[k] A :=
  (((Algebra.TensorProduct.comm k' (K ⊗[k] k') A).trans
      (Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[k'] A)
        (Algebra.TensorProduct.commRight k k' K).symm)).trans
      (Algebra.TensorProduct.cancelBaseChange k k' k' A K)).toRingEquiv.trans
    (Algebra.TensorProduct.comm k A K).toRingEquiv

/-- The canonical map from the self-tensor square of an algebra to the self-tensor
square of its scalar extension. -/
noncomputable def diagonalBaseChange (A : Type u) (A' : Type v) (B : Type w)
    [CommRing A] [CommRing A'] [CommRing B] [Algebra A A'] [Algebra A B] :
    B ⊗[A] B →ₐ[A] (A' ⊗[A] B) ⊗[A'] (A' ⊗[A] B) :=
  let i : B →ₐ[A] A' ⊗[A] B := includeRight
  let left : (A' ⊗[A] B) →ₐ[A] (A' ⊗[A] B) ⊗[A'] (A' ⊗[A] B) :=
    (includeLeft : (A' ⊗[A] B) →ₐ[A'] (A' ⊗[A] B) ⊗[A'] (A' ⊗[A] B)).restrictScalars A
  let right : (A' ⊗[A] B) →ₐ[A] (A' ⊗[A] B) ⊗[A'] (A' ⊗[A] B) :=
    (includeRight : (A' ⊗[A] B) →ₐ[A'] (A' ⊗[A] B) ⊗[A'] (A' ⊗[A] B)).restrictScalars A
  productMap (left.comp i) (right.comp i)

/-- The diagonal base-change map sends a pure tensor to the corresponding pair of
base-changed pure tensors. -/
theorem diagonalBaseChange_tmul (A : Type u) (A' : Type v) (B : Type w)
    [CommRing A] [CommRing A'] [CommRing B] [Algebra A A'] [Algebra A B] (b₁ b₂ : B) :
    diagonalBaseChange A A' B (b₁ ⊗ₜ[A] b₂) =
      ((1 : A') ⊗ₜ[A] b₁) ⊗ₜ[A'] ((1 : A') ⊗ₜ[A] b₂) := sorry

/-- The map on tensor squares induced by compatible maps of the base ring and
the algebra. -/
noncomputable def diagonalMap
    (A A₁ : Type u) (B B₁ : Type v)
    [CommRing A] [CommRing A₁] [CommRing B] [CommRing B₁]
    [Algebra A A₁] [Algebra A B] [Algebra A₁ B₁] [Algebra A B₁]
    [IsScalarTower A A₁ B₁] [Algebra B B₁] [IsScalarTower A B B₁] :
    B ⊗[A] B →ₐ[A] B₁ ⊗[A₁] B₁ :=
  let i : B →ₐ[A] B₁ := IsScalarTower.toAlgHom A B B₁
  let left : B₁ →ₐ[A] B₁ ⊗[A₁] B₁ :=
    (includeLeft : B₁ →ₐ[A₁] B₁ ⊗[A₁] B₁).restrictScalars A
  let right : B₁ →ₐ[A] B₁ ⊗[A₁] B₁ :=
    (includeRight : B₁ →ₐ[A₁] B₁ ⊗[A₁] B₁).restrictScalars A
  productMap (left.comp i) (right.comp i)

/-- The induced map on tensor squares sends a pure tensor to the pure tensor
obtained by applying the algebra map in each factor. -/
theorem diagonalMap_tmul
    (A A₁ : Type u) (B B₁ : Type v)
    [CommRing A] [CommRing A₁] [CommRing B] [CommRing B₁]
    [Algebra A A₁] [Algebra A B] [Algebra A₁ B₁] [Algebra A B₁]
    [IsScalarTower A A₁ B₁] [Algebra B B₁] [IsScalarTower A B B₁]
    (b c : B) :
    diagonalMap A A₁ B B₁ (b ⊗ₜ[A] c) =
      algebraMap B B₁ b ⊗ₜ[A₁] algebraMap B B₁ c := sorry

end Algebra.TensorProduct
