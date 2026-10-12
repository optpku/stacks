/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.TensorPower.Symmetric

@[expose] public section

open scoped TensorProduct

/-!
# Functoriality of symmetric tensor powers

This file supplies the map induced on an arbitrary-index symmetric tensor power by a
linear map of modules. The construction belongs at the semiring level and does not require the
index type to be finite.
-/

namespace SymmetricPower

universe u v w x

section

variable {R : Type u} [CommSemiring R]
variable {M₁ : Type v} [AddCommMonoid M₁] [Module R M₁]
variable {M : Type w} [AddCommMonoid M] [Module R M]
variable {M₂ : Type x} [AddCommMonoid M₂] [Module R M₂]
variable {ι : Type u}

namespace Internal

/-- The tensor-power map respects the symmetric-power permutation relation. -/
theorem mapRel {ι : Type u} (g : M₁ →ₗ[R] M)
    {x y : ⨂[R] (_ : ι), M₁}
    (h : addConGen (Rel R ι M₁) x y) :
    addConGen (Rel R ι M)
      (PiTensorProduct.map (fun _ ↦ g) x)
      (PiTensorProduct.map (fun _ ↦ g) y) := sorry

end Internal

/-- The linear map between `ι`-indexed symmetric powers induced by a linear map of modules. -/
@[stacks 00DO]
noncomputable def map (g : M₁ →ₗ[R] M) :
    Sym[R] ι M₁ →ₗ[R] Sym[R] ι M where
  __ :=
    AddCon.lift _
      (AddMonoidHom.comp (AddCon.mk' _) (PiTensorProduct.map (fun _ ↦ g)).toAddMonoidHom)
      (fun x y h ↦ Quotient.sound (Internal.mapRel g h))
  map_smul' r q := by
    refine AddCon.induction_on q ?_
    intro x
    change ((addConGen (Rel R ι M₁)).lift
        ((addConGen (Rel R ι M)).mk'.comp (PiTensorProduct.map (fun _ ↦ g)).toAddMonoidHom)
        (fun a b h ↦ Quotient.sound (Internal.mapRel g h)))
      ((SymmetricPower.smul' ι M₁ r) ((addConGen (Rel R ι M₁)).mk' x)) = _
    have hs₁ :
        SymmetricPower.smul' ι M₁ r ((addConGen (Rel R ι M₁)).mk' x) =
          ((addConGen (Rel R ι M₁)).mk' (r • x) : Sym[R] ι M₁) := rfl
    rw [hs₁, AddCon.lift_mk']
    change ((addConGen (Rel R ι M)).mk' (PiTensorProduct.map (fun _ ↦ g) (r • x)) :
        Sym[R] ι M) =
      SymmetricPower.smul' ι M r
        ((addConGen (Rel R ι M)).mk' (PiTensorProduct.map (fun _ ↦ g) x) :
          Sym[R] ι M)
    have hs₂ :
        SymmetricPower.smul' ι M r
            (((addConGen (Rel R ι M)).mk' (PiTensorProduct.map (fun _ ↦ g) x) :
              Sym[R] ι M)) =
          ((addConGen (Rel R ι M)).mk' (r • PiTensorProduct.map (fun _ ↦ g) x) :
            Sym[R] ι M) := rfl
    rw [hs₂]
    simp

/-- `SymmetricPower.map` on a quotient representative. -/
@[simp] theorem map_mk {ι : Type u} (g : M₁ →ₗ[R] M) (x : ⨂[R] (_ : ι), M₁) :
    map g (SymmetricPower.mk R ι M₁ x) =
      SymmetricPower.mk R ι M (PiTensorProduct.map (fun _ ↦ g) x) := sorry

/-- `SymmetricPower.map` on a pure symmetric tensor. -/
@[simp] theorem map_tprod {ι : Type u} (g : M₁ →ₗ[R] M) (m : ι → M₁) :
    map g (SymmetricPower.tprod R m) = SymmetricPower.tprod R (g ∘ m) := sorry

/-- Symmetric-power maps preserve identity linear maps. -/
@[simp] theorem map_id (ι : Type u) :
    map (ι := ι) (LinearMap.id : M₁ →ₗ[R] M₁) = LinearMap.id := sorry

/-- Symmetric-power maps preserve composition of linear maps. -/
@[simp] theorem map_comp (ι : Type u) (f : M₁ →ₗ[R] M) (g : M →ₗ[R] M₂) :
    map (ι := ι) (g ∘ₗ f) = map g ∘ₗ map f := sorry

/-- A surjective linear map induces a surjective map on every symmetric tensor power. -/
@[stacks 00DO]
theorem map_surjective {ι : Type u} (g : M₁ →ₗ[R] M) (hg : Function.Surjective g) :
    Function.Surjective (map (ι := ι) g) := sorry

end

end SymmetricPower
