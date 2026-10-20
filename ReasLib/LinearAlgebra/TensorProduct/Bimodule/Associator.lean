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

/- The `letI` is a deliberate defeq pin: the right-factor action is noncanonical in Mathlib and is
   therefore kept scoped rather than made a global instance. -/
/-- The base and right-factor actions on `X ⊗[R] Y` commute. -/
@[stacks 00D2 "transported base/right scalar commutation"]
theorem smulCommClassBase :
    -- Local instance justification (defeq pin): the class is indexed by this scoped right-factor action.
    letI : Module S (X ⊗[R] Y) := rightModule
    SMulCommClass R S (X ⊗[R] Y) := sorry

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
                map_zero' := sorry
                map_add' := sorry }
            map_zero' := sorry
            map_add' := sorry }
        map_zero' := sorry
        map_add' := sorry }
      (fun a m n ↦ sorry)
  let hom : ((M ⊗[A] N) ⊗[B] P) →+ M ⊗[A] (N ⊗[B] P) :=
    liftAddHom curry (fun b x p ↦ sorry)
  let invCurry : M →+ (N ⊗[B] P) →+ ((M ⊗[A] N) ⊗[B] P) :=
    { toFun := fun m ↦
        liftAddHom
          { toFun := fun n ↦
              { toFun := fun p ↦ (m ⊗ₜ[A] n : M ⊗[A] N) ⊗ₜ[B] p
                map_zero' := sorry
                map_add' := sorry }
            map_zero' := sorry
            map_add' := sorry }
          (fun b n p ↦ sorry)
      map_zero' := sorry
      map_add' := sorry }
  let inv : (M ⊗[A] (N ⊗[B] P)) →+ ((M ⊗[A] N) ⊗[B] P) :=
    liftAddHom invCurry (fun a m x ↦ sorry)
  { toFun := hom
    invFun := inv
    left_inv := sorry
    right_inv := sorry
    map_add' := hom.map_add }

/-- The mixed-base associator sends a pure tensor to its right-associated form. -/
@[simp, stacks 00D2]
theorem assoc_tmul (m : M) (n : N) (p : P) :
    assoc ((m ⊗ₜ[A] n : M ⊗[A] N) ⊗ₜ[B] p) = m ⊗ₜ[A] (n ⊗ₜ[B] p) := sorry

/-- The inverse mixed-base associator sends a right-associated pure tensor backwards. -/
@[simp, stacks 00D2]
theorem assoc_symm_tmul (m : M) (n : N) (p : P) :
    assoc.symm (m ⊗ₜ[A] (n ⊗ₜ[B] p)) = (m ⊗ₜ[A] n : M ⊗[A] N) ⊗ₜ[B] p := sorry

/-- The mixed-base associator as an `A`-linear equivalence. -/
@[stacks 00D2 "A-linear associator"]
noncomputable def assocLeft :
    ((M ⊗[A] N) ⊗[B] P) ≃ₗ[A] M ⊗[A] (N ⊗[B] P) :=
  AddEquiv.toLinearEquiv assoc (fun a x ↦ sorry)

/-- The same mixed-base associator viewed as a `B`-linear equivalence. -/
@[stacks 00D2]
noncomputable def assocRight :
    ((M ⊗[A] N) ⊗[B] P) ≃ₗ[B] M ⊗[A] (N ⊗[B] P) :=
  AddEquiv.toLinearEquiv assoc (fun b x ↦ sorry)

/-- The `A`-linear view and the bundled associator have the same underlying map. -/
@[simp, stacks 00D2]
theorem assocLeft_apply (x : (M ⊗[A] N) ⊗[B] P) :
    assocLeft x = assoc x := sorry

/-- The `B`-linear view and the bundled associator have the same underlying map. -/
@[simp, stacks 00D2]
theorem assocRight_apply (x : (M ⊗[A] N) ⊗[B] P) :
    assocRight x = assoc x := sorry

/-- The inverse `A`-linear view and the inverse bundled associator have the same underlying map. -/
@[simp, stacks 00D2]
theorem assocLeft_symm_apply (x : M ⊗[A] (N ⊗[B] P)) :
    assocLeft.symm x = assoc.symm x := sorry

/-- The inverse `B`-linear view and the inverse bundled associator have the same underlying map. -/
@[simp, stacks 00D2]
theorem assocRight_symm_apply (x : M ⊗[A] (N ⊗[B] P)) :
    assocRight.symm x = assoc.symm x := sorry

end Assoc

end TensorProduct.Bimodule
