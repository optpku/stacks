/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.TensorPower.Symmetric
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The universal lift from a symmetric tensor power

A multilinear map descends to a symmetric tensor power exactly when it is invariant under
permuting its inputs.  This file packages that quotient lift as concrete linear data, so later
constructions do not need to repeat the underlying `AddCon` descent.
-/

@[expose] public section

open scoped TensorProduct

noncomputable section

universe u v w

namespace SymmetricPower

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {N : Type w} [AddCommMonoid N] [Module R N]
variable {ι : Type u}

/-- A multilinear map is symmetric when it is invariant under every permutation of its
arguments. -/
def IsInvariant (f : MultilinearMap R (fun _ : ι ↦ M) N) : Prop :=
  ∀ (e : Equiv.Perm ι) (m : ι → M), f (m ∘ e) = f m

/-- The tensor-power lift of a symmetric multilinear map respects the congruence defining the
symmetric tensor power. -/
theorem piTensorLift_eq_of_rel
    (f : MultilinearMap R (fun _ : ι ↦ M) N) (hf : IsInvariant f) :
    addConGen (Rel R ι M) ≤
      AddCon.ker (PiTensorProduct.lift f).toAddMonoidHom := by
  apply AddCon.addConGen_le.mpr
  intro x y h
  cases h with
  | perm e m =>
    apply (AddCon.ker_rel _).mpr
    change PiTensorProduct.lift f (PiTensorProduct.tprod R m) =
      PiTensorProduct.lift f (PiTensorProduct.tprod R (m ∘ e))
    simpa only [PiTensorProduct.lift.tprod] using (hf e m).symm

/-- The additive quotient lift of a symmetric multilinear map. -/
noncomputable def liftAddHom
    (f : MultilinearMap R (fun _ : ι ↦ M) N) (hf : IsInvariant f) :
    Sym[R] ι M →+ N :=
  AddCon.lift _ (PiTensorProduct.lift f).toAddMonoidHom
    (piTensorLift_eq_of_rel f hf)

/-- The additive symmetric-power lift commutes with scalar multiplication. -/
theorem liftAddHom_smul
    (f : MultilinearMap R (fun _ : ι ↦ M) N) (hf : IsInvariant f)
    (r : R) (x : Sym[R] ι M) :
    liftAddHom f hf (r • x) = r • liftAddHom f hf x := by
  refine AddCon.induction_on x ?_
  intro y
  change PiTensorProduct.lift f (r • y) = r • PiTensorProduct.lift f y
  exact (PiTensorProduct.lift f).map_smul r y

/-- The linear map from a symmetric tensor power induced by a symmetric multilinear map. -/
@[stacks 01CF "universal property of symmetric powers"]
noncomputable def lift
    (f : MultilinearMap R (fun _ : ι ↦ M) N) (hf : IsInvariant f) :
    Sym[R] ι M →ₗ[R] N where
  __ := liftAddHom f hf
  map_smul' := liftAddHom_smul f hf

/-- The symmetric-power lift evaluates on a tensor representative by the original tensor-power
lift. -/
@[simp]
theorem lift_mk
    (f : MultilinearMap R (fun _ : ι ↦ M) N) (hf : IsInvariant f)
    (x : ⨂[R] (_ : ι), M) :
    lift f hf (SymmetricPower.mk R ι M x) = PiTensorProduct.lift f x := by
  rfl

/-- The symmetric-power lift evaluates on a pure symmetric tensor by the original multilinear
map. -/
@[simp]
theorem lift_tprod
    (f : MultilinearMap R (fun _ : ι ↦ M) N) (hf : IsInvariant f)
    (m : ι → M) :
    lift f hf (SymmetricPower.tprod R m) = f m := by
  change lift f hf (SymmetricPower.mk R ι M (PiTensorProduct.tprod R m)) = f m
  rw [lift_mk, PiTensorProduct.lift.tprod]

/-- A linear map from a symmetric power induces a multilinear map by composition with the pure
symmetric tensor map. -/
noncomputable def compTprod (g : Sym[R] ι M →ₗ[R] N) :
    MultilinearMap R (fun _ : ι ↦ M) N :=
  g.compMultilinearMap (SymmetricPower.tprod R)

/-- The multilinear map induced by a linear map from a symmetric power evaluates by first taking
the pure symmetric tensor. -/
@[simp]
theorem compTprod_apply
    (g : Sym[R] ι M →ₗ[R] N) (m : ι → M) :
    compTprod g m = g (SymmetricPower.tprod R m) := by
  rfl

/-- The multilinear map induced by a map from a symmetric power is permutation-invariant. -/
theorem compTprod_isInvariant (g : Sym[R] ι M →ₗ[R] N) :
    IsInvariant (compTprod g) := by
  intro e m
  exact congrArg g (tprod_equiv e m)

/-- Composing a symmetric-power lift with the pure symmetric tensor map recovers the original
multilinear map. -/
@[simp]
theorem compTprod_lift
    (f : MultilinearMap R (fun _ : ι ↦ M) N) (hf : IsInvariant f) :
    compTprod (lift f hf) = f := by
  apply MultilinearMap.ext
  intro m
  exact lift_tprod f hf m

/-- Descending the multilinear map induced by a linear map from a symmetric power recovers the
original linear map. -/
@[simp]
theorem lift_compTprod (g : Sym[R] ι M →ₗ[R] N) :
    lift (compTprod g) (compTprod_isInvariant g) = g := by
  apply LinearMap.ext_on_range (span_tprod_eq_top R ι M)
  intro m
  exact lift_tprod (compTprod g) (compTprod_isInvariant g) m

/-- Linear maps out of a symmetric tensor power are determined by their values on pure symmetric
tensors. -/
theorem linearMap_ext
    {f g : Sym[R] ι M →ₗ[R] N}
    (h : ∀ m : ι → M, f (SymmetricPower.tprod R m) =
      g (SymmetricPower.tprod R m)) :
    f = g := by
  exact LinearMap.ext_on_range (span_tprod_eq_top R ι M) h

end SymmetricPower
