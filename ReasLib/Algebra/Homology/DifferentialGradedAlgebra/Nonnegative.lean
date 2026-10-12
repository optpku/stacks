/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
    (n : ℤ) + (m : ℤ) = ((n + m : ℕ) : ℤ) := sorry

/-- Casting between equal homogeneous degrees preserves addition. -/
theorem castLinearMap_map_add (A : ChainDGAlgebra.{u, v} R) {i j : ℤ} (h : i = j)
    (x y : A.X i) :
    cast (congrArg (fun n : ℤ ↦ (A.X n : Type v)) h) (x + y) =
      cast (congrArg (fun n : ℤ ↦ (A.X n : Type v)) h) x +
        cast (congrArg (fun n : ℤ ↦ (A.X n : Type v)) h) y := sorry

/-- Casting between equal homogeneous degrees preserves scalar multiplication. -/
theorem castLinearMap_map_smul (A : ChainDGAlgebra.{u, v} R) {i j : ℤ} (h : i = j)
    (r : R) (x : A.X i) :
    cast (congrArg (fun n : ℤ ↦ (A.X n : Type v)) h) (r • x) =
      r • cast (congrArg (fun n : ℤ ↦ (A.X n : Type v)) h) x := sorry

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
    A.nonnegativeMul x (0 : A.nonnegativePiece m) = 0 := sorry

/-- Restricted homogeneous multiplication sends a zero left factor to zero. -/
theorem zero_nonnegativeMul (A : ChainDGAlgebra.{u, v} R) {n m : ℕ}
    (y : A.nonnegativePiece m) :
    A.nonnegativeMul (0 : A.nonnegativePiece n) y = 0 := sorry

/-- Restricted homogeneous multiplication distributes over addition on the right. -/
theorem nonnegativeMul_add (A : ChainDGAlgebra.{u, v} R) {n m : ℕ}
    (x : A.nonnegativePiece n) (y z : A.nonnegativePiece m) :
    A.nonnegativeMul x (y + z) = A.nonnegativeMul x y + A.nonnegativeMul x z := sorry

/-- Restricted homogeneous multiplication distributes over addition on the left. -/
theorem add_nonnegativeMul (A : ChainDGAlgebra.{u, v} R) {n m : ℕ}
    (x y : A.nonnegativePiece n) (z : A.nonnegativePiece m) :
    A.nonnegativeMul (x + y) z = A.nonnegativeMul x z + A.nonnegativeMul y z := sorry

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
    1 * x = x := sorry

/-- The restricted homogeneous unit acts on the right. -/
theorem nonnegative_mul_one (A : ChainDGAlgebra.{u, v} R)
    (x : GradedMonoid A.nonnegativePiece) :
    x * 1 = x := sorry

/-- Restricted homogeneous multiplication is associative. -/
theorem nonnegative_mul_assoc (A : ChainDGAlgebra.{u, v} R)
    (x y z : GradedMonoid A.nonnegativePiece) :
    x * y * z = x * (y * z) := sorry

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
    A.nonnegativeNatCast 0 = 0 := sorry

/-- The restricted natural-number cast preserves successors. -/
theorem nonnegativeNatCast_succ (A : ChainDGAlgebra.{u, v} R) (n : ℕ) :
    A.nonnegativeNatCast (n + 1) = A.nonnegativeNatCast n + A.one := sorry

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
    A.nonnegativeAlgebraMap 1 = GradedMonoid.GOne.one := sorry

/-- The structural scalar map preserves multiplication. -/
theorem nonnegativeAlgebraMap_mul (A : ChainDGAlgebra.{u, v} R) (r s : R) :
    GradedMonoid.mk 0 (A.nonnegativeAlgebraMap (r * s)) =
      GradedMonoid.mk 0
        (GradedMonoid.GMul.mul (A.nonnegativeAlgebraMap r) (A.nonnegativeAlgebraMap s)) := sorry

/-- Scalars commute with every homogeneous element of the nonnegative restriction. -/
theorem nonnegativeAlgebraMap_commutes (A : ChainDGAlgebra.{u, v} R) (r : R)
    (x : GradedMonoid A.nonnegativePiece) :
    GradedMonoid.mk 0 (A.nonnegativeAlgebraMap r) * x =
      x * GradedMonoid.mk 0 (A.nonnegativeAlgebraMap r) := sorry

/-- Scalar multiplication agrees with multiplication by the degree-zero scalar image. -/
theorem nonnegativeAlgebraMap_smul (A : ChainDGAlgebra.{u, v} R) (r : R)
    (x : GradedMonoid A.nonnegativePiece) :
    r • x = GradedMonoid.mk 0 (A.nonnegativeAlgebraMap r) * x := sorry

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
        (((-1 : R) ^ (n * m)) • GradedMonoid.GMul.mul y x) := sorry

/-- Odd squares remain zero after restriction to nonnegative degrees. -/
theorem nonnegative_sq_eq_zero_of_odd (A : ChainDGAlgebra.{u, v} R) [A.IsStrictlyCommutative]
    {n : ℕ} (hn : Odd n) (x : A.nonnegativePiece n) :
    GradedMonoid.GMul.mul x x = 0 := sorry

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
      B.nonnegativeMul (f.toChainMap.f n x) (f.toChainMap.f m y) := sorry

/-- A chain-DGA homomorphism preserves the unit after restriction to nonnegative degrees. -/
theorem nonnegativePart_map_one (f : ChainDGAlgebra.Hom A B) :
    f.toChainMap.f 0 A.one = B.one := sorry

/-- Restriction of a chain-DGA homomorphism to the nonnegative graded algebras. -/
def nonnegativePart (f : ChainDGAlgebra.Hom A B) :
    NonnegGradedAlgebra.Hom A.nonnegativePart B.nonnegativePart where
  map n := (f.toChainMap.f n).hom
  map_one := f.nonnegativePart_map_one
  map_mul := f.nonnegativePart_map_mul

/-- The degree-`n` map of the nonnegative restriction is the corresponding chain-map
component. -/
@[simp] theorem nonnegativePart_map (f : ChainDGAlgebra.Hom A B) (n : ℕ) :
    f.nonnegativePart.map n = (f.toChainMap.f n).hom := sorry

/-- Restriction to the nonnegative part acts degreewise by the original chain-DGA map. -/
@[simp] theorem nonnegativePart_apply (f : ChainDGAlgebra.Hom A B)
    (n : ℕ) (x : A.nonnegativePiece n) :
    f.nonnegativePart n x = f n x := sorry

/-- Restricting the identity chain-DGA homomorphism gives the graded identity. -/
@[simp] theorem nonnegativePart_id (A : ChainDGAlgebra.{u, v} R) [A.IsStrictlyCommutative] :
    (ChainDGAlgebra.Hom.id A).nonnegativePart = 𝟙 A.nonnegativePart := sorry

/-- Restriction to nonnegative degrees preserves composition. -/
@[simp] theorem nonnegativePart_comp {C : ChainDGAlgebra.{u, v} R} [C.IsStrictlyCommutative]
    (g : ChainDGAlgebra.Hom B C) (f : ChainDGAlgebra.Hom A B) :
    (ChainDGAlgebra.Hom.comp g f).nonnegativePart =
      NonnegGradedAlgebra.Hom.comp g.nonnegativePart f.nonnegativePart := sorry

end Hom

/-- A chain DGA is nonnegative when its underlying integer chain complex is strictly supported
on the canonical embedding of natural chain degrees. -/
@[stacks 09PJ "nonnegative support of a chain differential graded algebra"]
abbrev IsNonnegative (A : ChainDGAlgebra.{u, v} R) : Prop :=
  A.toChainComplex.IsNonnegative

/-- Every negative homogeneous piece of a nonnegative chain DGA is a zero object. -/
theorem isZero_X_of_neg (A : ChainDGAlgebra.{u, v} R) [A.IsNonnegative]
    (n : ℤ) (hn : n < 0) : IsZero (A.X n) := sorry

/-- Vanishing of every negative homogeneous piece supplies the canonical nonnegative-support
instance for a chain DGA. -/
theorem isNonnegative_of_isZero_X_neg (A : ChainDGAlgebra.{u, v} R)
    (hA : ∀ n : ℤ, n < 0 → IsZero (A.X n)) : A.IsNonnegative := sorry

/-- Positive homology vanishes when every strictly positive homology object is zero. -/
def PositiveHomologyVanishes (A : ChainDGAlgebra.{u, v} R) : Prop :=
  ∀ n : ℕ+, IsZero (A.homology (n : ℤ))

/-- The target integer degree of a differential from a positive natural degree. -/
theorem positiveDifferential_index (n : ℕ+) :
    ((n : ℕ) : ℤ) - 1 = (((n : ℕ) - 1 : ℕ) : ℤ) := sorry

/-- The chain differential between two adjacent nonnegative homogeneous pieces. -/
def nonnegativeDifferential (A : ChainDGAlgebra.{u, v} R) (n : ℕ+) :
    A.nonnegativePiece n →ₗ[R] A.nonnegativePiece ((n : ℕ) - 1) :=
  (ModuleCat.castLinearMap A (positiveDifferential_index n)).comp (A.d n).hom

/-- The degree identity for the differential from a positive even piece to the preceding odd
piece. -/
theorem positiveEvenDifferential_index (d : ℕ) :
    (2 * ((d + 1 : ℕ) : ℤ)) - 1 = ((2 * d + 1 : ℕ) : ℤ) := sorry

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
