/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.DirectSum.NonnegGradedAlgebra.Hom
public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.Commutative
public import ReasLib.Algebra.Homology.Embedding.UpNat

/-!
# Nonnegative restrictions of chain differential graded algebras

This file restricts the integer grading of a chain DGA to natural degrees and packages those
pieces as a canonical `NonnegGradedAlgebra`.  It also exposes the positive-even differential
needed by parity-sensitive constructions.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped DirectSum

universe u v

namespace ChainDGAlgebra

variable {R : Type u} [CommRing R]

/-- The nonnegative homogeneous pieces of a chain differential graded algebra. -/
abbrev nonnegativePiece (A : ChainDGAlgebra.{u, v} R) (n : ℕ) : Type v :=
  A.X n

/-- Coercion from natural degrees preserves addition in the integer grading. -/
theorem ofNat_add (n m : ℕ) :
    (n : ℤ) + (m : ℤ) = ((n + m : ℕ) : ℤ) := by
  exact (Nat.cast_add n m).symm

/-- Casting between equal homogeneous degrees preserves addition. -/
theorem castLinearMap_map_add (A : ChainDGAlgebra.{u, v} R) {i j : ℤ} (h : i = j)
    (x y : A.X i) :
    cast (congrArg (fun n : ℤ ↦ (A.X n : Type v)) h) (x + y) =
      cast (congrArg (fun n : ℤ ↦ (A.X n : Type v)) h) x +
        cast (congrArg (fun n : ℤ ↦ (A.X n : Type v)) h) y := by
  subst h
  rfl

/-- Casting between equal homogeneous degrees preserves scalar multiplication. -/
theorem castLinearMap_map_smul (A : ChainDGAlgebra.{u, v} R) {i j : ℤ} (h : i = j)
    (r : R) (x : A.X i) :
    cast (congrArg (fun n : ℤ ↦ (A.X n : Type v)) h) (r • x) =
      r • cast (congrArg (fun n : ℤ ↦ (A.X n : Type v)) h) x := by
  subst h
  rfl

/-- The linear transport between two equal homogeneous degrees. -/
def ModuleCat.castLinearMap (A : ChainDGAlgebra.{u, v} R) {i j : ℤ} (h : i = j) :
    A.X i →ₗ[R] A.X j where
  toFun x := cast (congrArg (fun n : ℤ ↦ (A.X n : Type v)) h) x
  map_add' := A.castLinearMap_map_add h
  map_smul' := A.castLinearMap_map_smul h

/-- Homogeneous multiplication restricted to nonnegative degrees. -/
def nonnegativeMul (A : ChainDGAlgebra.{u, v} R) {n m : ℕ}
    (x : A.nonnegativePiece n) (y : A.nonnegativePiece m) :
    A.nonnegativePiece (n + m) :=
  ModuleCat.castLinearMap A (ofNat_add n m) (A.mul n m x y)

/-- Restricted homogeneous multiplication sends a zero right factor to zero. -/
theorem nonnegativeMul_zero (A : ChainDGAlgebra.{u, v} R) {n m : ℕ}
    (x : A.nonnegativePiece n) :
    A.nonnegativeMul x (0 : A.nonnegativePiece m) = 0 := by
  unfold nonnegativeMul
  rw [map_zero, map_zero]

/-- Restricted homogeneous multiplication sends a zero left factor to zero. -/
theorem zero_nonnegativeMul (A : ChainDGAlgebra.{u, v} R) {n m : ℕ}
    (y : A.nonnegativePiece m) :
    A.nonnegativeMul (0 : A.nonnegativePiece n) y = 0 := by
  unfold nonnegativeMul
  rw [map_zero, LinearMap.zero_apply, map_zero]

/-- Restricted homogeneous multiplication distributes over addition on the right. -/
theorem nonnegativeMul_add (A : ChainDGAlgebra.{u, v} R) {n m : ℕ}
    (x : A.nonnegativePiece n) (y z : A.nonnegativePiece m) :
    A.nonnegativeMul x (y + z) = A.nonnegativeMul x y + A.nonnegativeMul x z := by
  unfold nonnegativeMul
  rw [map_add, map_add]

/-- Restricted homogeneous multiplication distributes over addition on the left. -/
theorem add_nonnegativeMul (A : ChainDGAlgebra.{u, v} R) {n m : ℕ}
    (x y : A.nonnegativePiece n) (z : A.nonnegativePiece m) :
    A.nonnegativeMul (x + y) z = A.nonnegativeMul x z + A.nonnegativeMul y z := by
  unfold nonnegativeMul
  rw [map_add, LinearMap.add_apply, map_add]

private theorem smul_nonnegativeMul (A : ChainDGAlgebra.{u, v} R) {n m : ℕ}
    (r : R) (x : A.nonnegativePiece n) (y : A.nonnegativePiece m) :
    A.nonnegativeMul (r • x) y = r • A.nonnegativeMul x y := by
  unfold nonnegativeMul
  rw [map_smul, LinearMap.smul_apply, map_smul]

private theorem nonnegativeMul_smul (A : ChainDGAlgebra.{u, v} R) {n m : ℕ}
    (r : R) (x : A.nonnegativePiece n) (y : A.nonnegativePiece m) :
    A.nonnegativeMul x (r • y) = r • A.nonnegativeMul x y := by
  unfold nonnegativeMul
  rw [map_smul, map_smul]

private theorem mul_cast_heq (A : ChainDGAlgebra.{u, v} R) {i i' j j' : ℤ}
    (hi : i = i') (hj : j = j') (x : A.X i) (y : A.X j) :
    HEq (A.mul i' j'
      (cast (congrArg (fun n : ℤ ↦ (A.X n : Type v)) hi) x)
      (cast (congrArg (fun n : ℤ ↦ (A.X n : Type v)) hj) y))
      (A.mul i j x y) := by
  subst hi
  subst hj
  rfl

/-- The restricted multiplication operation on nonnegative homogeneous pieces. -/
noncomputable instance nonnegativeGMul (A : ChainDGAlgebra.{u, v} R) :
    GradedMonoid.GMul A.nonnegativePiece where
  mul := A.nonnegativeMul

/-- The restricted unit in homogeneous degree zero. -/
noncomputable instance nonnegativeGOne (A : ChainDGAlgebra.{u, v} R) :
    GradedMonoid.GOne A.nonnegativePiece where
  one := A.one

/-- The restricted homogeneous unit acts on the left. -/
theorem nonnegative_one_mul (A : ChainDGAlgebra.{u, v} R)
    (x : GradedMonoid A.nonnegativePiece) :
    1 * x = x := by
  rcases x with ⟨n, x⟩
  apply Sigma.ext (Nat.zero_add n)
  exact (cast_heq (congrArg (fun i : ℤ ↦ (A.X i : Type v)) (ofNat_add 0 n))
    (A.mul 0 n A.one x)).trans (heq_of_cast_eq _ (A.one_mul n x))

/-- The restricted homogeneous unit acts on the right. -/
theorem nonnegative_mul_one (A : ChainDGAlgebra.{u, v} R)
    (x : GradedMonoid A.nonnegativePiece) :
    x * 1 = x := by
  rcases x with ⟨n, x⟩
  apply Sigma.ext (Nat.add_zero n)
  exact (cast_heq (congrArg (fun i : ℤ ↦ (A.X i : Type v)) (ofNat_add n 0))
    (A.mul n 0 x A.one)).trans (heq_of_cast_eq _ (A.mul_one n x))

/-- Restricted homogeneous multiplication is associative. -/
theorem nonnegative_mul_assoc (A : ChainDGAlgebra.{u, v} R)
    (x y z : GradedMonoid A.nonnegativePiece) :
    x * y * z = x * (y * z) := by
  rcases x with ⟨i, a⟩
  rcases y with ⟨j, b⟩
  rcases z with ⟨k, c⟩
  apply Sigma.ext (Nat.add_assoc i j k)
  change HEq (A.nonnegativeMul (A.nonnegativeMul a b) c)
    (A.nonnegativeMul a (A.nonnegativeMul b c))
  have h := (mul_cast_heq A (ofNat_add i j) rfl (A.mul i j a b) c).trans
    ((heq_of_cast_eq _ (A.mul_assoc i j k a b c)).trans
      (mul_cast_heq A rfl (ofNat_add j k) a (A.mul j k b c)).symm)
  simpa only [nonnegativeMul, ModuleCat.castLinearMap, LinearMap.coe_mk,
    AddHom.coe_mk, cast_heq_iff_heq, heq_cast_iff_heq, cast_eq] using h

/-- The nonnegative pieces inherit the nonunital distributive laws. -/
noncomputable instance nonnegativeGNonUnitalNonAssocSemiring (A : ChainDGAlgebra.{u, v} R) :
    DirectSum.GNonUnitalNonAssocSemiring A.nonnegativePiece where
  mul_zero := A.nonnegativeMul_zero
  zero_mul := A.zero_nonnegativeMul
  mul_add := A.nonnegativeMul_add
  add_mul := A.add_nonnegativeMul

/-- The nonnegative pieces inherit the graded monoid laws. -/
noncomputable instance nonnegativeGMonoid (A : ChainDGAlgebra.{u, v} R) :
    GradedMonoid.GMonoid A.nonnegativePiece where
  one_mul := A.nonnegative_one_mul
  mul_one := A.nonnegative_mul_one
  mul_assoc := A.nonnegative_mul_assoc

/-- The natural-number cast in degree zero of the nonnegative restriction. -/
def nonnegativeNatCast (A : ChainDGAlgebra.{u, v} R) (n : ℕ) : A.nonnegativePiece 0 :=
  n • A.one

/-- The restricted natural-number cast sends zero to zero. -/
theorem nonnegativeNatCast_zero (A : ChainDGAlgebra.{u, v} R) :
    A.nonnegativeNatCast 0 = 0 := by
  exact zero_nsmul A.one

/-- The restricted natural-number cast preserves successors. -/
theorem nonnegativeNatCast_succ (A : ChainDGAlgebra.{u, v} R) (n : ℕ) :
    A.nonnegativeNatCast (n + 1) = A.nonnegativeNatCast n + A.one := by
  exact succ_nsmul A.one n

/-- The nonnegative pieces of a chain DGA form a graded semiring. -/
noncomputable instance nonnegativeGSemiring (A : ChainDGAlgebra.{u, v} R) :
    DirectSum.GSemiring A.nonnegativePiece where
  natCast := A.nonnegativeNatCast
  natCast_zero := A.nonnegativeNatCast_zero
  natCast_succ := A.nonnegativeNatCast_succ

/-- The structural scalar map into degree zero of the nonnegative restriction. -/
def nonnegativeAlgebraMap (A : ChainDGAlgebra.{u, v} R) : R →+ A.nonnegativePiece 0 :=
  (LinearMap.toSpanSingleton R (A.X 0) A.one).toAddMonoidHom

/-- The structural scalar map preserves one. -/
theorem nonnegativeAlgebraMap_one (A : ChainDGAlgebra.{u, v} R) :
    A.nonnegativeAlgebraMap 1 = GradedMonoid.GOne.one := by
  exact one_smul R A.one

/-- The structural scalar map preserves multiplication. -/
theorem nonnegativeAlgebraMap_mul (A : ChainDGAlgebra.{u, v} R) (r s : R) :
    GradedMonoid.mk 0 (A.nonnegativeAlgebraMap (r * s)) =
      GradedMonoid.mk 0
        (GradedMonoid.GMul.mul (A.nonnegativeAlgebraMap r) (A.nonnegativeAlgebraMap s)) := by
  apply congrArg (GradedMonoid.mk 0)
  change (r * s) • A.one = A.nonnegativeMul (r • A.one) (s • A.one)
  rw [smul_nonnegativeMul, nonnegativeMul_smul]
  exact (mul_smul r s A.one).trans
    (congrArg (fun x ↦ r • (s • x)) (A.one_mul 0 A.one).symm)

/-- Scalars commute with every homogeneous element of the nonnegative restriction. -/
theorem nonnegativeAlgebraMap_commutes (A : ChainDGAlgebra.{u, v} R) (r : R)
    (x : GradedMonoid A.nonnegativePiece) :
    GradedMonoid.mk 0 (A.nonnegativeAlgebraMap r) * x =
      x * GradedMonoid.mk 0 (A.nonnegativeAlgebraMap r) := by
  rcases x with ⟨n, x⟩
  calc
    GradedMonoid.mk 0 (A.nonnegativeAlgebraMap r) * GradedMonoid.mk n x =
        r • (1 * GradedMonoid.mk n x) := by
      change GradedMonoid.mk (0 + n) (A.nonnegativeMul (r • A.one) x) =
        GradedMonoid.mk (0 + n) (r • A.nonnegativeMul A.one x)
      rw [smul_nonnegativeMul]
    _ = r • GradedMonoid.mk n x :=
      congrArg (fun y : GradedMonoid A.nonnegativePiece ↦ r • y)
        (A.nonnegative_one_mul _)
    _ = r • (GradedMonoid.mk n x * 1) :=
      congrArg (fun y : GradedMonoid A.nonnegativePiece ↦ r • y)
        (A.nonnegative_mul_one _).symm
    _ = GradedMonoid.mk n x * GradedMonoid.mk 0 (A.nonnegativeAlgebraMap r) := by
      change GradedMonoid.mk (n + 0) (r • A.nonnegativeMul x A.one) =
        GradedMonoid.mk (n + 0) (A.nonnegativeMul x (r • A.one))
      rw [nonnegativeMul_smul]

/-- Scalar multiplication agrees with multiplication by the degree-zero scalar image. -/
theorem nonnegativeAlgebraMap_smul (A : ChainDGAlgebra.{u, v} R) (r : R)
    (x : GradedMonoid A.nonnegativePiece) :
    r • x = GradedMonoid.mk 0 (A.nonnegativeAlgebraMap r) * x := by
  rcases x with ⟨n, x⟩
  calc
    r • GradedMonoid.mk n x = r • (1 * GradedMonoid.mk n x) :=
      congrArg (fun y : GradedMonoid A.nonnegativePiece ↦ r • y)
        (A.nonnegative_one_mul _).symm
    _ = GradedMonoid.mk 0 (A.nonnegativeAlgebraMap r) * GradedMonoid.mk n x := by
      change GradedMonoid.mk (0 + n) (r • A.nonnegativeMul A.one x) =
        GradedMonoid.mk (0 + n) (A.nonnegativeMul (r • A.one) x)
      rw [smul_nonnegativeMul]

/-- The nonnegative pieces inherit the graded `R`-algebra structure. -/
noncomputable instance nonnegativeGAlgebra (A : ChainDGAlgebra.{u, v} R) :
    DirectSum.GAlgebra R A.nonnegativePiece where
  toFun := A.nonnegativeAlgebraMap
  map_one := A.nonnegativeAlgebraMap_one
  map_mul := A.nonnegativeAlgebraMap_mul
  commutes := A.nonnegativeAlgebraMap_commutes
  smul_def := A.nonnegativeAlgebraMap_smul

/-- Graded commutativity restricts from integer degrees to nonnegative degrees. -/
theorem nonnegative_mul_comm (A : ChainDGAlgebra.{u, v} R) [A.IsCommutative]
    (n m : ℕ) (x : A.nonnegativePiece n) (y : A.nonnegativePiece m) :
    GradedMonoid.GMul.mul x y =
      cast (congrArg A.nonnegativePiece (Nat.add_comm m n))
        (((-1 : R) ^ (n * m)) • GradedMonoid.GMul.mul y x) := by
  change cast (congrArg (fun i : ℤ ↦ (A.X i : Type v)) (ofNat_add n m))
      (A.mul _ _ x y) =
    cast (congrArg A.nonnegativePiece (Nat.add_comm m n))
      (((-1 : R) ^ (n * m)) •
        cast (congrArg (fun i : ℤ ↦ (A.X i : Type v)) (ofNat_add m n))
          (A.mul _ _ y x))
  rw [IsCommutative.mul_comm x y]
  rw [← Nat.cast_mul, Int.cast_negOnePow_natCast]
  rw [← A.castLinearMap_map_smul (ofNat_add m n)]
  simp only [cast_cast]

/-- Odd squares remain zero after restriction to nonnegative degrees. -/
theorem nonnegative_sq_eq_zero_of_odd (A : ChainDGAlgebra.{u, v} R) [A.IsStrictlyCommutative]
    {n : ℕ} (hn : Odd n) (x : A.nonnegativePiece n) :
    GradedMonoid.GMul.mul x x = 0 := by
  change ModuleCat.castLinearMap A (ofNat_add n n) (A.mul n n x x) = 0
  rw [IsStrictlyCommutative.sq_eq_zero_of_odd hn.natCast x, map_zero]

/-- Strict graded commutativity restricts canonically to the nonnegative pieces. -/
noncomputable instance nonnegativeIsStrictlyCommutative
    (A : ChainDGAlgebra.{u, v} R) [A.IsStrictlyCommutative] :
    DirectSum.Graded.IsStrictlyCommutative R A.nonnegativePiece where
  mul_comm := A.nonnegative_mul_comm
  sq_eq_zero_of_odd := A.nonnegative_sq_eq_zero_of_odd

/-- The canonical nonnegatively graded algebra obtained by discarding the negative pieces of a
strictly commutative chain DGA. -/
noncomputable def nonnegativePart (A : ChainDGAlgebra.{u, v} R) [A.IsStrictlyCommutative] :
    NonnegGradedAlgebra.{u, v} R where
  piece := A.nonnegativePiece
  pieceAddCommGroup := fun _ ↦ inferInstance
  pieceModule := fun _ ↦ inferInstance
  pieceGSemiring := A.nonnegativeGSemiring
  pieceGAlgebra := A.nonnegativeGAlgebra
  pieceIsStrictlyCommutative := A.nonnegativeIsStrictlyCommutative

namespace Hom

variable {A B : ChainDGAlgebra.{u, v} R} [A.IsStrictlyCommutative] [B.IsStrictlyCommutative]

/-- A chain-DGA homomorphism preserves multiplication after restriction to nonnegative degrees. -/
theorem nonnegativePart_map_mul (f : ChainDGAlgebra.Hom A B)
    (n m : ℕ) (x : A.nonnegativePiece n) (y : A.nonnegativePiece m) :
    f.toChainMap.f (n + m) (A.nonnegativeMul x y) =
      B.nonnegativeMul (f.toChainMap.f n x) (f.toChainMap.f m y) := by
  have hcast {i j : ℤ} (h : i = j) (a : A.X i) :
      f.toChainMap.f j (ModuleCat.castLinearMap A h a) =
        ModuleCat.castLinearMap B h (f.toChainMap.f i a) := by
    subst h
    rfl
  exact (hcast (ofNat_add n m) (A.mul n m x y)).trans
    (congrArg (ModuleCat.castLinearMap B (ofNat_add n m)) (f.map_mul n m x y))

/-- A chain-DGA homomorphism preserves the unit after restriction to nonnegative degrees. -/
theorem nonnegativePart_map_one (f : ChainDGAlgebra.Hom A B) :
    f.toChainMap.f 0 A.one = B.one := by
  exact f.map_one

/-- Restriction of a chain-DGA homomorphism to the nonnegative graded algebras. -/
def nonnegativePart (f : ChainDGAlgebra.Hom A B) :
    NonnegGradedAlgebra.Hom A.nonnegativePart B.nonnegativePart where
  map n := (f.toChainMap.f n).hom
  map_one := f.nonnegativePart_map_one
  map_mul := f.nonnegativePart_map_mul

/-- The degree-`n` map of the nonnegative restriction is the corresponding chain-map
component. -/
@[simp] theorem nonnegativePart_map (f : ChainDGAlgebra.Hom A B) (n : ℕ) :
    f.nonnegativePart.map n = (f.toChainMap.f n).hom := by
  rfl

/-- Restriction to the nonnegative part acts degreewise by the original chain-DGA map. -/
@[simp] theorem nonnegativePart_apply (f : ChainDGAlgebra.Hom A B)
    (n : ℕ) (x : A.nonnegativePiece n) :
    f.nonnegativePart n x = f n x := by
  rfl

/-- Restricting the identity chain-DGA homomorphism gives the graded identity. -/
@[simp] theorem nonnegativePart_id (A : ChainDGAlgebra.{u, v} R) [A.IsStrictlyCommutative] :
    (ChainDGAlgebra.Hom.id A).nonnegativePart = 𝟙 A.nonnegativePart := by
  rfl

/-- Restriction to nonnegative degrees preserves composition. -/
@[simp] theorem nonnegativePart_comp {C : ChainDGAlgebra.{u, v} R} [C.IsStrictlyCommutative]
    (g : ChainDGAlgebra.Hom B C) (f : ChainDGAlgebra.Hom A B) :
    (ChainDGAlgebra.Hom.comp g f).nonnegativePart =
      NonnegGradedAlgebra.Hom.comp g.nonnegativePart f.nonnegativePart := by
  rfl

end Hom

/-- A chain DGA is nonnegative when its underlying integer chain complex is strictly supported
on the canonical embedding of natural chain degrees. -/
@[stacks 09PJ "nonnegative support of a chain differential graded algebra"]
abbrev IsNonnegative (A : ChainDGAlgebra.{u, v} R) : Prop :=
  A.toChainComplex.IsNonnegative

/-- Every negative homogeneous piece of a nonnegative chain DGA is a zero object. -/
theorem isZero_X_of_neg (A : ChainDGAlgebra.{u, v} R) [A.IsNonnegative]
    (n : ℤ) (hn : n < 0) : IsZero (A.X n) := by
  apply A.toChainComplex.isZero_X_of_isStrictlySupported
    ComplexShape.embeddingDownNatInt n
  intro i hi
  change (i : ℤ) = n at hi
  have hnonneg := Int.natCast_nonneg i
  omega

/-- Vanishing of every negative homogeneous piece supplies the canonical nonnegative-support
instance for a chain DGA. -/
theorem isNonnegative_of_isZero_X_neg (A : ChainDGAlgebra.{u, v} R)
    (hA : ∀ n : ℤ, n < 0 → IsZero (A.X n)) : A.IsNonnegative := by
  refine ⟨fun n hn ↦ hA n ?_⟩
  by_contra h
  exact hn n.toNat (Int.toNat_of_nonneg (le_of_not_gt h))

/-- Positive homology vanishes when every strictly positive homology object is zero. -/
def PositiveHomologyVanishes (A : ChainDGAlgebra.{u, v} R) : Prop :=
  ∀ n : ℕ+, IsZero (A.homology (n : ℤ))

/-- The target integer degree of a differential from a positive natural degree. -/
theorem positiveDifferential_index (n : ℕ+) :
    ((n : ℕ) : ℤ) - 1 = (((n : ℕ) - 1 : ℕ) : ℤ) := by
  exact (Nat.cast_sub n.pos).symm

/-- The chain differential between two adjacent nonnegative homogeneous pieces. -/
def nonnegativeDifferential (A : ChainDGAlgebra.{u, v} R) (n : ℕ+) :
    A.nonnegativePiece n →ₗ[R] A.nonnegativePiece ((n : ℕ) - 1) :=
  (ModuleCat.castLinearMap A (positiveDifferential_index n)).comp (A.d n).hom

/-- The degree identity for the differential from a positive even piece to the preceding odd
piece. -/
theorem positiveEvenDifferential_index (d : ℕ) :
    (2 * ((d + 1 : ℕ) : ℤ)) - 1 = ((2 * d + 1 : ℕ) : ℤ) := by
  push_cast
  omega

/-- The differential from one positive even homogeneous piece to the preceding odd piece. -/
def positiveEvenDifferentialTerm (A : ChainDGAlgebra.{u, v} R) (d : ℕ) :
    A.nonnegativePiece (2 * (d + 1)) →ₗ[R] A.nonnegativePiece (2 * d + 1) :=
  (ModuleCat.castLinearMap A (positiveEvenDifferential_index d)).comp
    (A.d (2 * (d + 1))).hom

/-- The differential on the direct sum of all positive even pieces. -/
def positiveEvenDifferential (A : ChainDGAlgebra.{u, v} R) [A.IsStrictlyCommutative] :
    A.nonnegativePart.evenPositivePart →ₗ[R] A.nonnegativePart.oddPart :=
  DirectSum.toModule R ℕ A.nonnegativePart.oddPart fun d ↦
    (A.nonnegativePart.oddHom d).comp (A.positiveEvenDifferentialTerm d)
end ChainDGAlgebra
