module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import ReasLib.LinearAlgebra.TensorPower.Insertion.Slots

/-!
# Exterior-power relations from tensor-slot insertion

This leaf owns both the family-dependent presentation maps and the intrinsic
repeated-entry presentation of the exterior-power kernel.

@stack 00DP
-/

@[expose] public section

open scoped TensorProduct
open PiTensorProduct exteriorPower

universe u v w

namespace TensorPower.Insertion.Exterior

section Relations

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {I : Type w}

/-- Pure tensors with the same entry in two distinguished slots. -/
@[stacks 0H1C "repeated-entry tensor relations"]
def repeatSet (n : ℕ) : Set (⨂[R]^n M) :=
  {z | ∃ (p : SlotPair n) (m : Fin (n - 2) → M) (x : M),
    z = tprod R (insert n p x x m)}

/-- The skew-symmetry relation map attached to a family of generators. -/
@[stacks 00DP "canonical exterior swap relation map"]
noncomputable def swapMap (n : ℕ) (x : I → M) :
    (SlotPair n × I × I) → ⨂[R]^(n - 2) M →ₗ[R] ⨂[R]^n M
  | ⟨p, i₁, i₂⟩ =>
      twoSlotMap n p (x i₁) (x i₂) + twoSlotMap n p (x i₂) (x i₁)

/-- The repeated-entry relation map attached to a family of generators. -/
@[stacks 00DP "canonical exterior repeat relation map"]
noncomputable def repeatMap (n : ℕ) (x : I → M) :
    (SlotPair n × I) → ⨂[R]^(n - 2) M →ₗ[R] ⨂[R]^n M
  | ⟨p, i⟩ => twoSlotMap n p (x i) (x i)

/-- The direct-sum source for the exterior relation map. -/
@[stacks 00DP "canonical exterior relation source"]
abbrev Source (R : Type u) (M : Type v) (n : ℕ) (I : Type w)
    [CommSemiring R] [AddCommMonoid M] [Module R M] :=
  (((SlotPair n × I × I) →₀ ⨂[R]^(n - 2) M) ×
    ((SlotPair n × I) →₀ ⨂[R]^(n - 2) M))

/-- The family-level exterior relation map. -/
@[stacks 00DP]
noncomputable def relationMap (n : ℕ) (x : I → M) :
    Source R M n I →ₗ[R] ⨂[R]^n M :=
  let swaps := Finsupp.lsum R (fun a ↦ swapMap n x a)
  let repeats := Finsupp.lsum R (fun a ↦ repeatMap n x a)
  swaps.comp (LinearMap.fst R _ _) + repeats.comp (LinearMap.snd R _ _)

/-- The exterior relation map on one skew-symmetry summand. -/
@[simp]
theorem relationMap_fst_single (n : ℕ) (x : I → M)
    (p : SlotPair n) (i₁ i₂ : I) (z : ⨂[R]^(n - 2) M) :
    relationMap n x (Finsupp.single (p, i₁, i₂) z, 0) =
      twoSlotMap n p (x i₁) (x i₂) z +
        twoSlotMap n p (x i₂) (x i₁) z := by
  simp [relationMap, swapMap]

/-- The exterior relation map on one repeated-entry summand. -/
@[simp]
theorem relationMap_snd_single (n : ℕ) (x : I → M)
    (p : SlotPair n) (i : I) (z : ⨂[R]^(n - 2) M) :
    relationMap n x (0, Finsupp.single (p, i) z) =
      twoSlotMap n p (x i) (x i) z := by
  simp [relationMap, repeatMap]

/-- Pure-tensor formula for the skew-symmetry generator. -/
theorem relationMap_fst_tprod (n : ℕ) (x : I → M)
    (p : SlotPair n) (i₁ i₂ : I) (m : Fin (n - 2) → M) :
    relationMap n x (Finsupp.single (p, i₁, i₂) (tprod R m), 0) =
      tprod R (insert n p (x i₁) (x i₂) m) +
        tprod R (insert n p (x i₂) (x i₁) m) := by
  rw [relationMap_fst_single, twoSlotMap_tprod, twoSlotMap_tprod]

/-- Pure-tensor formula for the repeated-entry generator. -/
theorem relationMap_snd_tprod (n : ℕ) (x : I → M)
    (p : SlotPair n) (i : I) (m : Fin (n - 2) → M) :
    relationMap n x (0, Finsupp.single (p, i) (tprod R m)) =
      tprod R (insert n p (x i) (x i) m) := by
  rw [relationMap_snd_single, twoSlotMap_tprod]

end Relations

section Kernel

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {I : Type w}

/-- The tensor-to-exterior kernel is the span of tensors having two equal entries. -/
@[stacks 0H1C "exterior-power kernel as the repeated-entry span"]
theorem ker_eq_span_repeatSet (n : ℕ) :
    LinearMap.ker
        (PiTensorProduct.lift (ιMulti R n).toMultilinearMap :
          ⨂[R]^n M →ₗ[R] ⋀[R]^n M) =
      Submodule.span R (repeatSet (R := R) (M := M) n) := sorry

/-- A spanning family's exterior relation map is exactly the canonical kernel. -/
@[stacks 00DP]
theorem generator_ker_eq_range (n : ℕ) (x : I → M)
    (hx : Submodule.span R (Set.range x) = ⊤) :
    LinearMap.ker
        (PiTensorProduct.lift (ιMulti R n).toMultilinearMap :
          ⨂[R]^n M →ₗ[R] ⋀[R]^n M) =
      LinearMap.range (relationMap n x) := sorry

/-- Exactness part of the exterior generator presentation. -/
theorem generator_exact (n : ℕ) (x : I → M)
    (hx : Submodule.span R (Set.range x) = ⊤) :
    Function.Exact (relationMap n x)
      (PiTensorProduct.lift (ιMulti R n).toMultilinearMap) := sorry

/-- The canonical tensor-to-exterior map is surjective. -/
theorem generator_surjective (n : ℕ) :
    Function.Surjective (PiTensorProduct.lift (ιMulti R n).toMultilinearMap :
      ⨂[R]^n M →ₗ[R] ⋀[R]^n M) := sorry

/-- A spanning family gives an exact presentation of the exterior power. -/
@[stacks 00DP]
theorem generator_exact_sequence (n : ℕ) (x : I → M)
    (hx : Submodule.span R (Set.range x) = ⊤) :
    Function.Exact (relationMap n x)
        (PiTensorProduct.lift (ιMulti R n).toMultilinearMap) ∧
      Function.Surjective (PiTensorProduct.lift (ιMulti R n).toMultilinearMap :
        ⨂[R]^n M →ₗ[R] ⋀[R]^n M) := sorry

end Kernel

end TensorPower.Insertion.Exterior
