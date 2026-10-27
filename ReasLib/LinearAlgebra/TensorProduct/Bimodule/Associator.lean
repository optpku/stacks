/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.LinearAlgebra.TensorProduct.RightModule
import Mathlib.Tactic.CrossRefAttribute

open scoped TensorProduct TensorProduct.Right
open TensorProduct

@[expose] public section

namespace TensorProduct.Bimodule

universe u v w x y

/-!
# Mixed-base tensor associativity

@stack 00D2

The `TensorProduct.Bimodule` scope supplies the two transported scalar structures needed for a
mixed-base tensor tower.  The associator itself is an additive equivalence; its `A`- and `B`-linear
views are derived from the same underlying map.
-/

section Support

variable {R : Type u} [CommSemiring R]
variable {S : Type v} [Semiring S]
variable {X : Type w} [AddCommMonoid X] [Module R X] [Module S X]
variable [SMulCommClass S R X]
variable {Y : Type x} [AddCommMonoid Y] [Module R Y]

/-- The left-factor `S`-module on `X ⊗[R] Y` obtained from the opposite
commuting action. -/
@[stacks 00D2 "transported left-factor action"]
abbrev leftModule : Module S (X ⊗[R] Y) :=
  @TensorProduct.leftModule R S _ _ X Y _ _ _ _ _ (SMulCommClass.symm S R X)

end Support

section RightSupport

variable {R : Type u} [CommSemiring R]
variable {S : Type v} [Semiring S]
variable {X : Type w} [AddCommMonoid X] [Module R X]
variable {Y : Type x} [AddCommMonoid Y] [Module R Y] [Module S Y]
variable [SMulCommClass R S Y]

/- The right-factor action is a scoped choice in Mathlib; this name makes the choice explicit in
   the symmetric Bimodule support API without registering a competing global instance. -/
/-- The right-factor `S`-module on `X ⊗[R] Y` selected by the Bimodule scope. -/
@[stacks 00D2 "transported right-factor action"]
abbrev rightModule : Module S (X ⊗[R] Y) := TensorProduct.Right.module

end RightSupport

namespace Right

variable {R : Type u} [CommSemiring R]
variable {S : Type v} [Semiring S]
variable {X : Type w} [AddCommMonoid X] [Module R X]
variable {Y : Type x} [AddCommMonoid Y] [Module R Y] [Module S Y]
variable [SMulCommClass R S Y]

/-- The transported action scales the right component of a pure tensor. -/
theorem smul_tmul (s : S) (x : X) (y : Y) :
    letI : Module S (X ⊗[R] Y) := rightModule
    s • (x ⊗ₜ[R] y) = x ⊗ₜ[R] (s • y) := rfl

/- The `letI` is a deliberate defeq pin: the right-factor action is noncanonical in Mathlib and is
   therefore kept scoped rather than made a global instance. -/
/-- The base and right-factor actions on `X ⊗[R] Y` commute. -/
@[stacks 00D2 "transported base/right scalar commutation"]
theorem smulCommClassBase :
    -- Local instance justification (defeq pin): the class is indexed by this scoped right-factor action.
    letI : Module S (X ⊗[R] Y) := rightModule
    SMulCommClass R S (X ⊗[R] Y) := by
  letI : Module S (X ⊗[R] Y) := rightModule
  refine ⟨fun r s z ↦ ?_⟩
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      simp only [smul_tmul, ← TensorProduct.tmul_smul, smul_comm r s]
  | add x y hx hy => simp only [smul_add, hx, hy]

end Right

scoped[TensorProduct.Bimodule] attribute [instance 90] leftModule
scoped[TensorProduct.Bimodule] attribute [instance 100] rightModule
scoped[TensorProduct.Bimodule] attribute [instance 90] Right.smulCommClassBase

section Assoc

open scoped TensorProduct.Bimodule

variable {A : Type u} [CommSemiring A]
variable {B : Type v} [CommSemiring B]
variable {M : Type w} [AddCommMonoid M] [Module A M]
variable {N : Type x} [AddCommMonoid N] [Module A N] [Module B N]
variable [SMulCommClass A B N]
variable {P : Type y} [AddCommMonoid P] [Module B P]

/-- The canonical additive equivalence underlying mixed-base tensor reassociation.

The local names in the implementation only group the four deterministic maps supplied by the two
tensor-product universal properties; they do not select mathematical data or typeclass instances. -/
@[stacks 00D2 "additive associator"]
noncomputable def assoc :
    ((M ⊗[A] N) ⊗[B] P) ≃+ M ⊗[A] (N ⊗[B] P) :=
  let curry : M ⊗[A] N →+ P →+ M ⊗[A] (N ⊗[B] P) :=
    liftAddHom
      { toFun := fun m ↦
          { toFun := fun n ↦
              { toFun := fun p ↦ m ⊗ₜ[A] (n ⊗ₜ[B] p)
                map_zero' := by simp
                map_add' := by intros; simp [tmul_add] }
            map_zero' := by ext p; simp
            map_add' := by intros; ext p; simp [add_tmul, tmul_add] }
        map_zero' := by ext n p; simp
        map_add' := by intros; ext n p; simp [add_tmul] }
      (fun a m n ↦ by
        ext p
        exact TensorProduct.smul_tmul a m (n ⊗ₜ[B] p))
  let hom : ((M ⊗[A] N) ⊗[B] P) →+ M ⊗[A] (N ⊗[B] P) :=
    liftAddHom curry (fun b x p ↦ by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul m n =>
          change m ⊗ₜ[A] ((b • n) ⊗ₜ[B] p) = m ⊗ₜ[A] (n ⊗ₜ[B] (b • p))
          rw [TensorProduct.smul_tmul]
      | add x y hx hy =>
          simp only [smul_add, map_add, AddMonoidHom.add_apply, hx, hy])
  let invCurry : M →+ (N ⊗[B] P) →+ ((M ⊗[A] N) ⊗[B] P) :=
    { toFun := fun m ↦
        liftAddHom
          { toFun := fun n ↦
              { toFun := fun p ↦ (m ⊗ₜ[A] n : M ⊗[A] N) ⊗ₜ[B] p
                map_zero' := by simp
                map_add' := by intros; simp [tmul_add] }
            map_zero' := by ext p; simp
            map_add' := by intros; ext p; simp [tmul_add, add_tmul] }
          (fun b n p ↦ by
            change (b • (m ⊗ₜ[A] n)) ⊗ₜ[B] p =
              (m ⊗ₜ[A] n) ⊗ₜ[B] (b • p)
            exact TensorProduct.smul_tmul b (m ⊗ₜ[A] n) p)
      map_zero' := by
        ext x
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul n p => simp
        | add x y hx hy =>
            simp only [map_add, hx, hy, AddMonoidHom.zero_apply, add_zero]
      map_add' := by
        intro m₁ m₂
        ext x
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul n p => simp [add_tmul]
        | add x y hx hy => simp [map_add, hx, hy, add_add_add_comm] }
  let inv : (M ⊗[A] (N ⊗[B] P)) →+ ((M ⊗[A] N) ⊗[B] P) :=
    liftAddHom invCurry (fun a m x ↦ by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul n p =>
          change ((a • m) ⊗ₜ[A] n) ⊗ₜ[B] p =
            (m ⊗ₜ[A] (a • n)) ⊗ₜ[B] p
          rw [TensorProduct.smul_tmul]
      | add x y hx hy => simp only [smul_add, map_add, hx, hy])
  { toFun := hom
    invFun := inv
    left_inv := fun x ↦ by
      change inv (hom x) = x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul x p =>
          induction x using TensorProduct.induction_on with
          | zero => simp
          | tmul m n => rfl
          | add x y hx hy => simp only [add_tmul, map_add, hx, hy]
      | add x y hx hy => simp only [map_add, hx, hy]
    right_inv := fun x ↦ by
      change hom (inv x) = x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul m x =>
          induction x using TensorProduct.induction_on with
          | zero => simp
          | tmul n p => rfl
          | add x y hx hy => simp only [tmul_add, map_add, hx, hy]
      | add x y hx hy => simp only [map_add, hx, hy]
    map_add' := hom.map_add }

/-- The mixed-base associator sends a pure tensor to its right-associated form. -/
@[simp, stacks 00D2]
theorem assoc_tmul (m : M) (n : N) (p : P) :
    assoc ((m ⊗ₜ[A] n : M ⊗[A] N) ⊗ₜ[B] p) = m ⊗ₜ[A] (n ⊗ₜ[B] p) := rfl

/-- The inverse mixed-base associator sends a right-associated pure tensor backwards. -/
@[simp, stacks 00D2]
theorem assoc_symm_tmul (m : M) (n : N) (p : P) :
    assoc.symm (m ⊗ₜ[A] (n ⊗ₜ[B] p)) = (m ⊗ₜ[A] n : M ⊗[A] N) ⊗ₜ[B] p := rfl

/-- The mixed-base associator as an `A`-linear equivalence. -/
@[stacks 00D2 "A-linear associator"]
noncomputable def assocLeft :
    ((M ⊗[A] N) ⊗[B] P) ≃ₗ[A] M ⊗[A] (N ⊗[B] P) :=
  AddEquiv.toLinearEquiv assoc (fun a x ↦ by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x p =>
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul m n => simp only [TensorProduct.smul_tmul', assoc_tmul]
        | add x y hx hy => simp only [smul_add, add_tmul, map_add, hx, hy]
    | add x y hx hy => simp only [smul_add, map_add, hx, hy])

/-- The same mixed-base associator viewed as a `B`-linear equivalence. -/
@[stacks 00D2]
noncomputable def assocRight :
    ((M ⊗[A] N) ⊗[B] P) ≃ₗ[B] M ⊗[A] (N ⊗[B] P) :=
  AddEquiv.toLinearEquiv assoc (fun b x ↦ by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x p =>
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul m n =>
            simp only [TensorProduct.smul_tmul', Right.smul_tmul, assoc_tmul]
        | add x y hx hy => simp only [smul_add, add_tmul, map_add, hx, hy]
    | add x y hx hy => simp only [smul_add, map_add, hx, hy])

/-- The `A`-linear view and the bundled associator have the same underlying map. -/
@[simp, stacks 00D2]
theorem assocLeft_apply (x : (M ⊗[A] N) ⊗[B] P) :
    assocLeft x = assoc x := rfl

/-- The `B`-linear view and the bundled associator have the same underlying map. -/
@[simp, stacks 00D2]
theorem assocRight_apply (x : (M ⊗[A] N) ⊗[B] P) :
    assocRight x = assoc x := rfl

/-- The inverse `A`-linear view and the inverse bundled associator have the same underlying map. -/
@[simp, stacks 00D2]
theorem assocLeft_symm_apply (x : M ⊗[A] (N ⊗[B] P)) :
    assocLeft.symm x = assoc.symm x := rfl

/-- The inverse `B`-linear view and the inverse bundled associator have the same underlying map. -/
@[simp, stacks 00D2]
theorem assocRight_symm_apply (x : M ⊗[A] (N ⊗[B] P)) :
    assocRight.symm x = assoc.symm x := rfl

end Assoc

end TensorProduct.Bimodule
