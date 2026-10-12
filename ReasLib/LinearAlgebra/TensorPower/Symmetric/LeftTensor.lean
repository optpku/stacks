/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.LinearAlgebra.TensorPower.Symmetric.UFin

@[expose] public section

open scoped TensorProduct

/-!
# Left tensor maps for finite symmetric tensor powers

This file provides the finite-index comparison map which prepends a factor to a symmetric
tensor power. Its public source and target use `SymmetricPower.UFin`, the universe-adjusted
finite indexing type required by mathlib's symmetric tensor power construction.
-/

namespace SymmetricPower

universe u v w

section

variable {R : Type u} [CommSemiring R]
variable {M₂ : Type v} [AddCommMonoid M₂] [Module R M₂]
variable {M₁ : Type w} [AddCommMonoid M₁] [Module R M₁]

/-- Prepends a factor to a family indexed by `UFin n`. -/
def cons (x : M₁) (m : UFin n → M₁) : UFin (n + 1) → M₁
  | ⟨i⟩ => Fin.cases x (fun j ↦ m ⟨j⟩) i

namespace Internal

/-- Updating a tail commutes with `SymmetricPower.cons`. -/
theorem cons_update (x : M₁) (m : UFin n → M₁) (i : UFin n) (y : M₁) :
    cons x (Function.update m i y) = Function.update (cons x m) ⟨i.down.succ⟩ y := sorry

/-- The multilinear map underlying `SymmetricPower.leftTensorMap`. -/
noncomputable def prependMultilinear (n : ℕ) (x : M₁) :
    MultilinearMap R (fun _ : UFin n ↦ M₁) (Sym[R] (UFin (n + 1)) M₁) :=
  MultilinearMap.mk'
    (fun m ↦ SymmetricPower.tprod R (cons x m))
    (fun m i y z ↦ by
      let F : MultilinearMap R (fun _ : UFin (n + 1) ↦ M₁) (Sym[R] (UFin (n + 1)) M₁) :=
        SymmetricPower.tprod R
      simpa [F, cons_update] using F.map_update_add (cons x m) ⟨i.down.succ⟩ y z)
    (fun m i c y ↦ by
      let F : MultilinearMap R (fun _ : UFin (n + 1) ↦ M₁) (Sym[R] (UFin (n + 1)) M₁) :=
        SymmetricPower.tprod R
      simpa [F, cons_update] using F.map_update_smul (cons x m) ⟨i.down.succ⟩ c y)

/-- The tensor-power lift underlying `SymmetricPower.leftTensorMap`. -/
noncomputable def prependTensorMap (n : ℕ) :
    M₁ →ₗ[R] (⨂[R] (_ : UFin n), M₁) →ₗ[R] Sym[R] (UFin (n + 1)) M₁ where
  toFun x := PiTensorProduct.lift (prependMultilinear n x)
  map_add' x y := by
    classical
    ext m
    let F : MultilinearMap R (fun _ : UFin (n + 1) ↦ M₁) (Sym[R] (UFin (n + 1)) M₁) :=
      SymmetricPower.tprod R
    simp only [LinearMap.compMultilinearMap_apply, PiTensorProduct.lift.tprod, LinearMap.add_apply]
    change F (cons (x + y) m) = F (cons x m) + F (cons y m)
    have hxy :
        Function.update (cons (0 : M₁) m) (⟨0⟩ : UFin (n + 1)) (x + y) = cons (x + y) m := by
      ext j
      rcases j with ⟨j⟩
      cases j using Fin.cases <;> simp [cons, Function.update]
    have hx :
        Function.update (cons (0 : M₁) m) (⟨0⟩ : UFin (n + 1)) x = cons x m := by
      ext j
      rcases j with ⟨j⟩
      cases j using Fin.cases <;> simp [cons, Function.update]
    have hy :
        Function.update (cons (0 : M₁) m) (⟨0⟩ : UFin (n + 1)) y = cons y m := by
      ext j
      rcases j with ⟨j⟩
      cases j using Fin.cases <;> simp [cons, Function.update]
    rw [← hxy, ← hx, ← hy]
    exact F.map_update_add (cons (0 : M₁) m) (⟨0⟩ : UFin (n + 1)) x y
  map_smul' r x := by
    classical
    ext m
    let F : MultilinearMap R (fun _ : UFin (n + 1) ↦ M₁) (Sym[R] (UFin (n + 1)) M₁) :=
      SymmetricPower.tprod R
    simp only [LinearMap.compMultilinearMap_apply, PiTensorProduct.lift.tprod, LinearMap.smul_apply]
    change F (cons (r • x) m) = r • F (cons x m)
    have hrx :
        Function.update (cons (0 : M₁) m) (⟨0⟩ : UFin (n + 1)) (r • x) = cons (r • x) m := by
      ext j
      rcases j with ⟨j⟩
      cases j using Fin.cases <;> simp [cons, Function.update]
    have hx :
        Function.update (cons (0 : M₁) m) (⟨0⟩ : UFin (n + 1)) x = cons x m := by
      ext j
      rcases j with ⟨j⟩
      cases j using Fin.cases <;> simp [cons, Function.update]
    rw [← hrx, ← hx]
    exact F.map_update_smul (cons (0 : M₁) m) (⟨0⟩ : UFin (n + 1)) r x

/-- The tensor-power lift respects the symmetric-power permutation relation. -/
theorem prepend_eq (n : ℕ) (x : M₁)
    {y z : ⨂[R] (_ : UFin n), M₁}
    (h : addConGen (Rel R (UFin n) M₁) y z) :
    prependTensorMap n x y = prependTensorMap n x z := sorry

/-- The curried symmetric-power map used by `SymmetricPower.leftTensorMap`. -/
noncomputable def prependMap (n : ℕ) :
    M₁ →ₗ[R] Sym[R] (UFin n) M₁ →ₗ[R] Sym[R] (UFin (n + 1)) M₁ where
  toFun x :=
    { __ := AddCon.lift _ (prependTensorMap n x).toAddMonoidHom (fun _ _ h ↦ prepend_eq n x h)
      map_smul' r q := by
        refine AddCon.induction_on q ?_
        intro y
        change ((addConGen (Rel R (UFin n) M₁)).lift ((prependTensorMap n x).toAddMonoidHom)
            (fun a b h ↦ prepend_eq n x h))
          ((SymmetricPower.smul' (UFin n) M₁ r) ((addConGen (Rel R (UFin n) M₁)).mk' y)) = _
        rw [show
          SymmetricPower.smul' (UFin n) M₁ r ((addConGen (Rel R (UFin n) M₁)).mk' y) =
            ((addConGen (Rel R (UFin n) M₁)).mk' (r • y) : Sym[R] (UFin n) M₁) by
            rfl]
        simp
    }
  map_add' x y := by
    ext q
    refine AddCon.induction_on q ?_
    intro z
    simpa [LinearMap.add_apply] using congrArg (fun f ↦ f z) ((prependTensorMap n).map_add x y)
  map_smul' r x := by
    ext q
    refine AddCon.induction_on q ?_
    intro y
    simpa [LinearMap.smul_apply] using congrArg (fun f ↦ f y) ((prependTensorMap n).map_smulₛₗ r x)

end Internal

/-- The comparison map induced by `f` from a tensor with a `UFin n`-indexed symmetric power to
a `UFin (n + 1)`-indexed symmetric power. -/
noncomputable def leftTensorMap (n : ℕ) (f : M₂ →ₗ[R] M₁) :
    M₂ ⊗[R] Sym[R] (UFin n) M₁ →ₗ[R] Sym[R] (UFin (n + 1)) M₁ :=
  TensorProduct.lift (Internal.prependMap n ∘ₗ f)

/-- `SymmetricPower.leftTensorMap` on pure tensor factors. -/
@[simp] theorem leftTensorMap_tmul_tprod (n : ℕ) (f : M₂ →ₗ[R] M₁)
    (x : M₂) (m : UFin n → M₁) :
    leftTensorMap n f (x ⊗ₜ SymmetricPower.tprod R m) =
      SymmetricPower.tprod R (cons (f x) m) := sorry

end

end SymmetricPower
