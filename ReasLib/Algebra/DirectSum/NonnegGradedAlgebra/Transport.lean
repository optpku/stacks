/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.Iso
public import ReasLib.Algebra.DirectSum.NonnegGradedAlgebra.Hom

/-!
# Transport of nonnegative graded algebras

This leaf transports the algebra structure on a family of homogeneous modules through a
degreewise linear equivalence.  The chosen equivalence remains explicit: it is generally not
canonical, so the construction does not install any instance on the target family.  Instead it
returns a bundled `NonnegGradedAlgebra` together with its canonical comparison isomorphism.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v w

namespace NonnegGradedAlgebra.Transport

section Algebra

variable {R : Type u} [CommRing R]
variable (A : NonnegGradedAlgebra.{u, v} R)
variable {B : ℕ → Type w} [∀ n, AddCommGroup (B n)] [∀ n, Module R (B n)]
variable (e : ∀ n, A.piece n ≃ₗ[R] B n)

/-- Homogeneous multiplication transported degreewise through `e`. -/
def mul {m n : ℕ} (x : B m) (y : B n) : B (m + n) :=
  e (m + n) (GradedMonoid.GMul.mul ((e m).symm x) ((e n).symm y))

/-- The homogeneous unit transported to the target degree-zero piece. -/
def one : B 0 :=
  e 0 (GradedMonoid.GOne.one : A.piece 0)

/-- Multiplication by a transported zero vanishes on the right. -/
theorem mul_zero {m n : ℕ} (x : B m) : mul A e x (0 : B n) = 0 := sorry

/-- Multiplication by a transported zero vanishes on the left. -/
theorem zero_mul {m n : ℕ} (y : B n) : mul A e (0 : B m) y = 0 := sorry

/-- Transported homogeneous multiplication distributes over addition on the right. -/
theorem mul_add {m n : ℕ} (x : B m) (y z : B n) :
    mul A e x (y + z) = mul A e x y + mul A e x z := sorry

/-- Transported homogeneous multiplication distributes over addition on the left. -/
theorem add_mul {m n : ℕ} (x y : B m) (z : B n) :
    mul A e (x + y) z = mul A e x z + mul A e y z := sorry

/-- The transported unit is a left identity on the graded target family. -/
theorem one_mul (x : GradedMonoid B) :
    GradedMonoid.mk (0 + x.1) (mul A e (one A e) x.2) = x := sorry

/-- The transported unit is a right identity on the graded target family. -/
theorem mul_one (x : GradedMonoid B) :
    GradedMonoid.mk (x.1 + 0) (mul A e x.2 (one A e)) = x := sorry

/-- Transported homogeneous multiplication is associative. -/
theorem mul_assoc (x y z : GradedMonoid B) :
    GradedMonoid.mk ((x.1 + y.1) + z.1) (mul A e (mul A e x.2 y.2) z.2) =
      GradedMonoid.mk (x.1 + (y.1 + z.1)) (mul A e x.2 (mul A e y.2 z.2)) := sorry

/-- The graded natural-power operation transported degreewise through `e`. -/
def gnpow (n : ℕ) {i : ℕ} (x : B i) : B (n • i) :=
  e (n • i) (GradedMonoid.GMonoid.gnpow n ((e i).symm x))

/-- The zeroth transported graded power is the transported unit. -/
theorem gnpow_zero (x : GradedMonoid B) :
    GradedMonoid.mk (0 • x.1) (gnpow A e 0 x.2) = GradedMonoid.mk 0 (one A e) := sorry

/-- Transported graded powers satisfy the successor recursion. -/
theorem gnpow_succ (n : ℕ) (x : GradedMonoid B) :
    GradedMonoid.mk (n.succ • x.1) (gnpow A e n.succ x.2) =
      GradedMonoid.mk (n • x.1 + x.1) (mul A e (gnpow A e n x.2) x.2) := sorry

/-- The natural-number cast into the transported degree-zero piece. -/
def natCast (n : ℕ) : B 0 :=
  e 0 (DirectSum.GSemiring.natCast (A := A.piece) n)

/-- The transported natural-number cast sends zero to zero. -/
theorem natCast_zero : natCast A e 0 = 0 := sorry

/-- The transported natural-number cast preserves successors. -/
theorem natCast_succ (n : ℕ) :
    natCast A e (n + 1) = natCast A e n + one A e := sorry

/-- The structural scalar map into the transported degree-zero piece. -/
def algebraMap : R →+ B 0 :=
  (e 0).toLinearMap.toAddMonoidHom.comp
    (DirectSum.GAlgebra.toFun (R := R) (A := A.piece))

/-- The transported structural scalar map preserves the homogeneous unit. -/
theorem algebraMap_one : algebraMap A e 1 = one A e := sorry

/-- The transported structural scalar map preserves multiplication. -/
theorem algebraMap_mul (r s : R) :
    GradedMonoid.mk 0 (algebraMap A e (r * s)) =
      GradedMonoid.mk 0 (mul A e (algebraMap A e r) (algebraMap A e s)) := sorry

/-- Scalars commute with every element of the transported graded family. -/
theorem algebraMap_commutes (r : R) (x : GradedMonoid B) :
    GradedMonoid.mk (0 + x.1) (mul A e (algebraMap A e r) x.2) =
      GradedMonoid.mk (x.1 + 0) (mul A e x.2 (algebraMap A e r)) := sorry

/-- Scalar multiplication agrees with multiplication by the transported scalar image. -/
theorem algebraMap_smul (r : R) (x : GradedMonoid B) :
    r • x = GradedMonoid.mk (0 + x.1) (mul A e (algebraMap A e r) x.2) := sorry

/-- Transported multiplication satisfies the Koszul commutativity rule. -/
theorem mul_comm (m n : ℕ) (x : B m) (y : B n) :
    mul A e x y =
      cast (congrArg B (Nat.add_comm n m))
        (((-1 : R) ^ (m * n)) • mul A e y x) := sorry

/-- Squares of transported odd-degree homogeneous elements vanish. -/
theorem sq_eq_zero_of_odd {m : ℕ} (hm : Odd m) (x : B m) :
    mul A e x x = 0 := sorry

/-- The transported graded-semiring structure, kept as explicit data depending on `e`. -/
@[reducible]
def gSemiring : DirectSum.GSemiring B where
  mul := mul A e
  mul_zero := mul_zero A e
  zero_mul := zero_mul A e
  mul_add := mul_add A e
  add_mul := add_mul A e
  one := one A e
  one_mul := one_mul A e
  mul_one := mul_one A e
  mul_assoc := mul_assoc A e
  gnpow := gnpow A e
  gnpow_zero' := gnpow_zero A e
  gnpow_succ' := gnpow_succ A e
  natCast := natCast A e
  natCast_zero := natCast_zero A e
  natCast_succ := natCast_succ A e

/-- The transported graded-algebra structure relative to the explicitly transported semiring.
The scoped instance is required only because Mathlib indexes `DirectSum.GAlgebra` by a
`DirectSum.GSemiring`; its value remains the public datum `gSemiring A e`. -/
@[reducible]
def gAlgebra : @DirectSum.GAlgebra ℕ R B _ _ _ _ (gSemiring A e) :=
  letI : DirectSum.GSemiring B := gSemiring A e
  { toFun := algebraMap A e
    map_one := algebraMap_one A e
    map_mul := algebraMap_mul A e
    commutes := algebraMap_commutes A e
    smul_def := algebraMap_smul A e }

/-- Strict graded commutativity relative to the explicitly transported algebra structure. -/
theorem isStrictlyCommutative :
    @DirectSum.Graded.IsStrictlyCommutative R _ B _ _ (gSemiring A e) (gAlgebra A e) := sorry

/-- The nonnegative graded algebra obtained by transporting every operation through `e`.
The target family itself receives no global instances; all structure is owned by this bundle. -/
@[stacks 09PQ "infrastructure: degreewise transport of a nonnegative graded algebra"]
def algebra : NonnegGradedAlgebra.{u, w} R where
  piece := B
  pieceAddCommGroup := fun _ ↦ inferInstance
  pieceModule := fun _ ↦ inferInstance
  pieceGSemiring := gSemiring A e
  pieceGAlgebra := gAlgebra A e
  pieceIsStrictlyCommutative := isStrictlyCommutative A e

/-- Multiplication in the transported bundle is the explicit transported operation. -/
@[simp]
theorem algebra_mul {m n : ℕ} (x : (algebra A e).piece m)
    (y : (algebra A e).piece n) :
    GradedMonoid.GMul.mul x y = mul A e x y := sorry

/-- The unit in the transported bundle is the explicit transported unit. -/
@[simp]
theorem algebra_one :
    (GradedMonoid.GOne.one : (algebra A e).piece 0) = one A e := sorry

/-- Graded natural powers in the transported bundle are the explicit transported powers. -/
@[simp]
theorem algebra_gnpow (n i : ℕ) (x : (algebra A e).piece i) :
    GradedMonoid.GMonoid.gnpow n x = gnpow A e n x := sorry

/-- The natural-number cast in the transported bundle is the explicit transported cast. -/
@[simp]
theorem algebra_natCast (n : ℕ) :
    DirectSum.GSemiring.natCast (A := (algebra A e).piece) n = natCast A e n := sorry

/-- The scalar map in the transported bundle is the explicit transported scalar map. -/
@[simp]
theorem algebra_algebraMap (r : R) :
    DirectSum.GAlgebra.toFun (R := R) (A := (algebra A e).piece) r = algebraMap A e r := sorry

end Algebra

section Comparison

variable {R : Type u} [CommRing R]
variable (A : NonnegGradedAlgebra.{u, v} R)
variable {B : ℕ → Type v} [∀ n, AddCommGroup (B n)] [∀ n, Module R (B n)]
variable (e : ∀ n, A.piece n ≃ₗ[R] B n)

/-- The degreewise equivalence preserves the homogeneous unit. -/
theorem gradedHom_map_one :
    e 0 (GradedMonoid.GOne.one : A.piece 0) =
      (GradedMonoid.GOne.one : (algebra A e).piece 0) := sorry

/-- The degreewise equivalence preserves homogeneous multiplication. -/
theorem gradedHom_map_mul (m n : ℕ) (x : A.piece m) (y : A.piece n) :
    e (m + n) (GradedMonoid.GMul.mul x y) =
      mul A e (e m x) (e n y) := sorry

/-- The source-to-target graded-algebra homomorphism underlying transport. -/
def gradedHom : A ⟶ algebra A e where
  map n := (e n).toLinearMap
  map_one := gradedHom_map_one A e
  map_mul := gradedHom_map_mul A e

/-- The inverse degreewise equivalence preserves the transported homogeneous unit. -/
theorem gradedInvHom_map_one :
    (e 0).symm (GradedMonoid.GOne.one : (algebra A e).piece 0) =
      (GradedMonoid.GOne.one : A.piece 0) := sorry

/-- The inverse degreewise equivalence preserves transported homogeneous multiplication. -/
theorem gradedInvHom_map_mul (m n : ℕ) (x : (algebra A e).piece m)
    (y : (algebra A e).piece n) :
    (e (m + n)).symm (mul A e x y) =
      GradedMonoid.GMul.mul ((e m).symm x) ((e n).symm y) := sorry

/-- The target-to-source graded-algebra homomorphism underlying transport. -/
def gradedInvHom : algebra A e ⟶ A where
  map n := (e n).symm.toLinearMap
  map_one := gradedInvHom_map_one A e
  map_mul := gradedInvHom_map_mul A e

/-- The transported comparison followed by its inverse is the identity. -/
theorem gradedHom_comp_inv : gradedHom A e ≫ gradedInvHom A e = 𝟙 A := sorry

/-- The inverse transported comparison followed by the comparison is the identity. -/
theorem gradedInv_comp_hom : gradedInvHom A e ≫ gradedHom A e = 𝟙 (algebra A e) := sorry

/-- The canonical graded-algebra isomorphism associated to degreewise transport. -/
def gradedIso : A ≅ algebra A e where
  hom := gradedHom A e
  inv := gradedInvHom A e
  hom_inv_id := gradedHom_comp_inv A e
  inv_hom_id := gradedInv_comp_hom A e

/-- The homogeneous map of the forward transported isomorphism is `e`. -/
@[simp]
theorem gradedIso_hom_map (n : ℕ) :
    (gradedIso A e).hom.map n = (e n).toLinearMap := sorry

/-- The homogeneous map of the inverse transported isomorphism is `e.symm`. -/
@[simp]
theorem gradedIso_inv_map (n : ℕ) :
    (gradedIso A e).inv.map n = (e n).symm.toLinearMap := sorry

end Comparison

end NonnegGradedAlgebra.Transport
