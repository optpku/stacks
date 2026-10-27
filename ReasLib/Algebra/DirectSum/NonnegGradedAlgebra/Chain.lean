/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.DirectSum.NonnegGradedAlgebra.Hom
public import ReasLib.Algebra.Homology.ChainGradedAlgebra.Hom

/-!
# Extension by zero of nonnegative graded algebras

A nonnegatively graded algebra has a canonical chain grading: retain its natural-degree pieces
and put the zero module in every negative degree.  This file owns that construction, its action on
morphisms, and the resulting functor.  It lets APIs stated for integer-graded derivations be reused
without rebuilding the nonnegative algebra as a differential graded algebra.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v

namespace NonnegGradedAlgebra

variable {R : Type u} [CommRing R]

/-- The integer-indexed family obtained from a nonnegative graded algebra by extension by zero. -/
@[stacks 09PS "extension by zero of nonnegative graded pieces"]
abbrev chainPiece (A : NonnegGradedAlgebra.{u, v} R) : ℤ → ModuleCat.{v} R
  | .ofNat n => ModuleCat.of R (A.piece n)
  | .negSucc _ => ModuleCat.of R PUnit

/-- In a nonnegative degree, extension by zero returns the original homogeneous piece. -/
@[simp]
theorem chainPiece_ofNat (A : NonnegGradedAlgebra.{u, v} R) (n : ℕ) :
    A.chainPiece n = ModuleCat.of R (A.piece n) := rfl

/-- In a negative degree, extension by zero returns the zero module. -/
@[simp]
theorem chainPiece_negSucc (A : NonnegGradedAlgebra.{u, v} R) (n : ℕ) :
    A.chainPiece (.negSucc n) = ModuleCat.of R PUnit := rfl

/-- Homogeneous multiplication on the extension-by-zero chain grading. -/
@[stacks 09PS "multiplication on the extension-by-zero chain grading"]
def chainMul (A : NonnegGradedAlgebra.{u, v} R) :
    ∀ i j : ℤ, A.chainPiece i →ₗ[R] A.chainPiece j →ₗ[R] A.chainPiece (i + j)
  | .ofNat _, .ofNat _ => DirectSum.gMulLHom R A.piece
  | .ofNat _, .negSucc _ => 0
  | .negSucc _, .ofNat _ => 0
  | .negSucc _, .negSucc _ => 0

/-- On nonnegative homogeneous pieces, chain multiplication is the original graded
multiplication. -/
@[simp]
theorem chainMul_ofNat (A : NonnegGradedAlgebra.{u, v} R) (n m : ℕ)
    (x : A.piece n) (y : A.piece m) :
    A.chainMul n m x y = GradedMonoid.GMul.mul x y := rfl

/-- The unit of the extension-by-zero chain grading. -/
def chainOne (A : NonnegGradedAlgebra.{u, v} R) : A.chainPiece 0 :=
  (GradedMonoid.GOne.one : A.piece 0)

/-- Extension-by-zero chain multiplication is associative. -/
theorem chainMul_assoc (A : NonnegGradedAlgebra.{u, v} R)
    (i j k : ℤ) (x : A.chainPiece i) (y : A.chainPiece j) (z : A.chainPiece k) :
    cast (congrArg (fun n : ℤ ↦ (A.chainPiece n : Type v)) (add_assoc i j k))
        (A.chainMul (i + j) k (A.chainMul i j x y) z) =
      A.chainMul i (j + k) x (A.chainMul j k y z) := by
  have cast_zero {a b : ℤ} (h : a = b) :
      cast (congrArg (fun n : ℤ ↦ (A.chainPiece n : Type v)) h)
        (0 : A.chainPiece a) = (0 : A.chainPiece b) := by
    cases h
    rfl
  cases i with
  | ofNat i =>
    cases j with
    | ofNat j =>
      cases k with
      | ofNat k =>
        apply eq_of_heq
        rw [cast_heq_iff_heq]
        exact (Sigma.mk.inj_iff.mp
          (mul_assoc (GradedMonoid.mk i x) (GradedMonoid.mk j y)
            (GradedMonoid.mk k z))).2
      | negSucc k =>
        have hz : z = 0 := Subsingleton.elim _ _
        rw [hz]
        simp only [map_zero]
        exact cast_zero (add_assoc (Int.ofNat i) (Int.ofNat j) (Int.negSucc k))
    | negSucc j =>
      have hy : y = 0 := Subsingleton.elim _ _
      rw [hy]
      simp only [map_zero, LinearMap.zero_apply]
      exact cast_zero (add_assoc (Int.ofNat i) (Int.negSucc j) k)
  | negSucc i =>
    have hx : x = 0 := Subsingleton.elim _ _
    rw [hx]
    simp only [map_zero, LinearMap.zero_apply]
    exact cast_zero (add_assoc (Int.negSucc i) j k)

/-- The extension-by-zero unit acts on the left. -/
theorem chainOne_mul (A : NonnegGradedAlgebra.{u, v} R)
    (i : ℤ) (x : A.chainPiece i) :
    cast (congrArg (fun n : ℤ ↦ (A.chainPiece n : Type v)) (zero_add i))
      (A.chainMul 0 i A.chainOne x) = x := by
  cases i with
  | ofNat n =>
    apply eq_of_heq
    rw [cast_heq_iff_heq]
    exact (Sigma.mk.inj_iff.mp (one_mul (GradedMonoid.mk n x))).2
  | negSucc n => exact Subsingleton.elim _ _

/-- The extension-by-zero unit acts on the right. -/
theorem chainMul_one (A : NonnegGradedAlgebra.{u, v} R)
    (i : ℤ) (x : A.chainPiece i) :
    cast (congrArg (fun n : ℤ ↦ (A.chainPiece n : Type v)) (add_zero i))
      (A.chainMul i 0 x A.chainOne) = x := by
  cases i with
  | ofNat n =>
    apply eq_of_heq
    rw [cast_heq_iff_heq]
    exact (Sigma.mk.inj_iff.mp (mul_one (GradedMonoid.mk n x))).2
  | negSucc n => exact Subsingleton.elim _ _

/-- The chain-graded algebra obtained from a nonnegative graded algebra by extension by zero. -/
@[stacks 09PS "chain grading associated to a nonnegative graded algebra"]
def toChainGradedAlgebra (A : NonnegGradedAlgebra.{u, v} R) :
    ChainGradedAlgebra.{u, v} R where
  X := A.chainPiece
  mul := A.chainMul
  one := A.chainOne
  mul_assoc := A.chainMul_assoc
  one_mul := A.chainOne_mul
  mul_one := A.chainMul_one

namespace Hom

variable {A B C : NonnegGradedAlgebra.{u, v} R}

/-- The degreewise linear family obtained by extending a nonnegative graded homomorphism by
zero. -/
def chainMap (f : Hom A B) :
    ∀ i : ℤ, A.chainPiece i →ₗ[R] B.chainPiece i
  | .ofNat n => f.map n
  | .negSucc _ => 0

/-- Extension by zero of a graded homomorphism preserves the unit. -/
theorem chainMap_one (f : Hom A B) :
    f.chainMap 0 A.toChainGradedAlgebra.one = B.toChainGradedAlgebra.one := by
  exact f.map_one

/-- Extension by zero of a graded homomorphism preserves homogeneous multiplication. -/
theorem chainMap_mul (f : Hom A B) (i j : ℤ)
    (x : A.toChainGradedAlgebra.X i) (y : A.toChainGradedAlgebra.X j) :
    f.chainMap (i + j) (A.toChainGradedAlgebra.mul i j x y) =
      B.toChainGradedAlgebra.mul i j (f.chainMap i x) (f.chainMap j y) := by
  cases i with
  | ofNat n =>
    cases j with
    | ofNat m => exact f.map_mul n m x y
    | negSucc m => exact map_zero _
  | negSucc n =>
    cases j with
    | ofNat m => exact map_zero _
    | negSucc m => exact map_zero _

/-- Extension by zero of a nonnegative graded-algebra homomorphism. -/
@[stacks 09PS "extension by zero of a nonnegative graded homomorphism"]
def toChainGradedHom (f : Hom A B) :
    A.toChainGradedAlgebra ⟶ B.toChainGradedAlgebra where
  map := f.chainMap
  map_one := f.chainMap_one
  map_mul := f.chainMap_mul

/-- Extension by zero preserves identity homomorphisms. -/
@[simp]
theorem toChainGradedHom_id (A : NonnegGradedAlgebra.{u, v} R) :
    toChainGradedHom (Hom.id A) = 𝟙 A.toChainGradedAlgebra := by
  apply ChainGradedAlgebra.Hom.ext_map
  intro i
  cases i with
  | ofNat n => rfl
  | negSucc n =>
    apply LinearMap.ext
    intro x
    exact Subsingleton.elim (α := PUnit) _ _

/-- Extension by zero preserves composition of homomorphisms. -/
@[simp]
theorem toChainGradedHom_comp (f : Hom A B) (g : Hom B C) :
    toChainGradedHom (Hom.comp g f) = toChainGradedHom f ≫ toChainGradedHom g := by
  apply ChainGradedAlgebra.Hom.ext_map
  intro i
  cases i with
  | ofNat n => rfl
  | negSucc n =>
    apply LinearMap.ext
    intro x
    rfl

end Hom

/-- Extension by zero from nonnegative graded algebras to chain-graded algebras. -/
@[stacks 09PS "extension-by-zero functor for nonnegative graded algebras"]
def toChainGraded (R : Type u) [CommRing R] :
    NonnegGradedAlgebra.{u, v} R ⥤ ChainGradedAlgebra.{u, v} R where
  obj A := A.toChainGradedAlgebra
  map f := Hom.toChainGradedHom f
  map_id A := Hom.toChainGradedHom_id A
  map_comp f g := Hom.toChainGradedHom_comp f g

end NonnegGradedAlgebra
