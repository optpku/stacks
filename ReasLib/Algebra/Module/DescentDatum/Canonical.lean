/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import ReasLib.Algebra.Module.DescentDatum

/-!
# The canonical module descent datum

An `R`-module determines descent data on its scalar extension to `A`. The
comparison interchanges the first scalar factor with the original module.
-/

@[expose] public section

noncomputable section

open CategoryTheory ModuleCat
open scoped ChangeOfRings TensorProduct TensorProduct.Right

namespace Module.DescentDatum

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-- The explicit comparison for the canonical descent datum on `M ⊗[R] A`.
It sends `(m ⊗ₜ a) ⊗ₜ a'` to `a ⊗ₜ (m ⊗ₜ a')`. -/
noncomputable def canonicalEquiv (M : ModuleCat.{u} R) :
    (M ⊗[R] A) ⊗[R] A ≃ₗ[A ⊗[R] A] A ⊗[R] (M ⊗[R] A) :=
  let e : (M ⊗[R] A) ⊗[R] A ≃ₗ[R] A ⊗[R] (M ⊗[R] A) :=
    TensorProduct.assoc R M A A ≪≫ₗ TensorProduct.leftComm R M A A
  { toFun := e
    invFun := e.symm
    left_inv := e.left_inv
    right_inv := e.right_inv
    map_add' := e.map_add
    map_smul' := by
      intro s x
      change e (s • x) = s • e x
      induction s using TensorProduct.induction_on with
      | zero => simp
      | add s t hs ht => simp only [add_smul, map_add, hs, ht]
      | tmul a b =>
        induction x using TensorProduct.induction_on with
        | zero => simp
        | add x y hx hy => simp only [smul_add, map_add, hx, hy]
        | tmul x c =>
          induction x using TensorProduct.induction_on with
          | zero => simp
          | add x y hx hy => simp only [TensorProduct.add_tmul, smul_add, map_add, hx, hy]
          | tmul m d => rfl }

/-- The canonical descent comparison has the expected value on pure tensors. -/
theorem canonicalEquiv_tmul (M : ModuleCat.{u} R) (m : M) (a a' : A) :
    canonicalEquiv R A M ((m ⊗ₜ[R] a) ⊗ₜ[R] a') =
      a ⊗ₜ[R] (m ⊗ₜ[R] a') := rfl

/-- Commuting the tensor factors identifies the right-oriented scalar extension
`M ⊗[R] A` with `ModuleCat.extendScalars (algebraMap R A) M`. -/
noncomputable def canonicalModuleIso (M : ModuleCat.{u} R) :
    ModuleCat.of A (M ⊗[R] A) ≅
      (ModuleCat.extendScalars (algebraMap R A)).obj M :=
  let restrictedA :=
    (ModuleCat.restrictScalars (algebraMap R A)).obj (ModuleCat.of A A)
  let scalarIso : A ≃ₗ[R] restrictedA :=
    { toFun := id
      invFun := id
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r a ↦ Algebra.smul_def r a }
  let e : M ⊗[R] A ≃ₗ[R] restrictedA ⊗[R] M :=
    TensorProduct.comm R M A ≪≫ₗ
      TensorProduct.congr scalarIso (LinearEquiv.refl R M)
  let eA : M ⊗[R] A ≃ₗ[A]
      (ModuleCat.extendScalars (algebraMap R A)).obj M :=
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_add' := e.map_add
      map_smul' := by
        let e' : M ⊗[R] A ≃+
            (ModuleCat.extendScalars (algebraMap R A)).obj M := e.toAddEquiv
        intro a x
        change e' (a • x) = a • e' x
        induction x using TensorProduct.induction_on with
        | zero => simp
        | add x y hx hy => simp only [smul_add, map_add, hx, hy]
        | tmul m b => rfl }
  eA.toModuleIso

/-- The normalization isomorphism sends `m ⊗ₜ a` to `a ⊗ₜ m`. -/
theorem canonicalModuleIso_hom_tmul (M : ModuleCat.{u} R) (m : M) (a : A) :
    (canonicalModuleIso R A M).hom (m ⊗ₜ[R] a) =
      a ⊗ₜ[R, algebraMap R A] m := rfl

/-- The canonical descent datum on the scalar extension `M ⊗[R] A`. -/
noncomputable def canonical (M : ModuleCat.{u} R) :
    Module.DescentDatum R A (M ⊗[R] A) :=
  Module.DescentDatum.ofEquiv (canonicalEquiv R A M) (by
    apply LinearMap.ext
    intro x
    change extend12 (canonicalEquiv R A M) (extend01 (canonicalEquiv R A M) x) =
      extend02 (canonicalEquiv R A M) x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x c =>
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
      | tmul x b =>
        induction x using TensorProduct.induction_on with
        | zero => simp
        | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
        | tmul m a => rfl)

/-- The equivalence stored in the canonical descent datum is `canonicalEquiv`. -/
theorem canonical_equiv (M : ModuleCat.{u} R) :
    (canonical R A M).equiv = canonicalEquiv R A M := rfl

end Module.DescentDatum
