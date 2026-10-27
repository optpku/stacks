/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DividedPowers.GradedAlgebra.AdjoinVariable
public import ReasLib.RingTheory.DividedPowers.GradedAlgebra.Category

/-!
# Bundled graded algebras obtained by adjoining one variable

This file promotes the coefficient families in `NonnegGradedAlgebra.Adjoin` to genuine bundled
nonnegatively graded algebras.  Multiplication is an explicit finite-support convolution on the
homogeneous coefficient pieces; only its algebraic laws are deferred as propositions.
-/

@[expose] public section

open CategoryTheory
open scoped DirectSum

noncomputable section

universe u v

namespace NonnegGradedAlgebra.Adjoin

variable {R : Type u} [CommRing R]

namespace Implementation

theorem cast_zero (A : NonnegGradedAlgebra.{u, v} R) {m n : ℕ} (h : m = n) :
    cast (congrArg A.piece h) (0 : A.piece m) = 0 := by
  cases h
  rfl

theorem cast_add (A : NonnegGradedAlgebra.{u, v} R) {m n : ℕ} (h : m = n)
    (x y : A.piece m) :
    cast (congrArg A.piece h) (x + y) =
      cast (congrArg A.piece h) x + cast (congrArg A.piece h) y := by
  cases h
  rfl

theorem cast_smul (A : NonnegGradedAlgebra.{u, v} R) {m n : ℕ} (h : m = n)
    (r : R) (x : A.piece m) :
    cast (congrArg A.piece h) (r • x) = r • cast (congrArg A.piece h) x := by
  cases h
  rfl

theorem pieceCast_apply (A : NonnegGradedAlgebra.{u, v} R) {m n : ℕ} (h : m = n)
    (x : A.piece m) : A.pieceCast h x = cast (congrArg A.piece h) x := by
  cases h
  rfl

theorem hom_map_cast {A B : NonnegGradedAlgebra.{u, v} R}
    (f : NonnegGradedAlgebra.Hom A B) {m n : ℕ} (h : m = n) (x : A.piece m) :
    f.map n (cast (congrArg A.piece h) x) =
      cast (congrArg B.piece h) (f.map m x) := by
  cases h
  rfl

theorem cast_roundtrip {α β : Type v} (h : α = β) (h' : β = α) (x : α) :
    cast h' (cast h x) = x := by
  cases h
  rfl

theorem cast_comp {α β γ : Type v} (h : α = β) (h' : β = γ) (h'' : α = γ) (x : α) :
    cast h' (cast h x) = cast h'' x := by
  cases h
  rfl

theorem recOn_eq_cast {ι : Type*} {β : ι → Type v} {i j : ι} (h : i = j) (x : β i) :
    Eq.recOn h x = cast (congrArg β h) x := by
  cases h
  rfl

theorem cast_single {ι : Type*} [DecidableEq ι]
    (A : NonnegGradedAlgebra.{u, v} R) (weight : ι → ℕ) {m n : ℕ} (h : m = n)
    (i : {i : ι // weight i ≤ m}) (x : A.piece (m - weight i)) :
    cast (congrArg (ShiftSum A weight) h) (DFinsupp.single i x) =
      DFinsupp.single (β := fun j : {j : ι // weight j ≤ n} ↦ A.piece (n - weight j))
        ⟨i.val, h ▸ i.property⟩
        (cast (congrArg A.piece (congrArg (fun q ↦ q - weight i) h)) x) := by
  cases h
  rfl

/-- Evaluation of a dependent finitely supported sum with its classical decidability arguments
made explicit, so adjoining constructions do not modify the ambient instance environment. -/
def sum {ι : Type*} {β : ι → Type*} [∀ i, Zero (β i)]
    {M : Type*} [AddCommMonoid M] (x : Π₀ i, β i) (f : ∀ i, β i → M) : M :=
  @DFinsupp.sum ι M β (Classical.decEq ι) _
    (fun _ xi ↦ Classical.propDecidable (xi ≠ 0)) _ x f

theorem sum_eq {ι : Type*} {β : ι → Type*} [∀ i, Zero (β i)]
    [DecidableEq ι] [∀ i (x : β i), Decidable (x ≠ 0)]
    {M : Type*} [AddCommMonoid M] (x : Π₀ i, β i) (f : ∀ i, β i → M) :
    sum x f = DFinsupp.sum x f := by
  exact congrArg₂
    (fun deq dne ↦ @DFinsupp.sum ι M β deq _ dne _ x f)
    (Subsingleton.elim _ _) (Subsingleton.elim _ _)

@[simp]
theorem sum_zero_index {ι : Type*} {β : ι → Type*} [∀ i, AddCommMonoid (β i)]
    {M : Type*} [AddCommMonoid M] (f : ∀ i, β i → M) :
    sum (0 : Π₀ i, β i) f = 0 := by
  classical
  rw [sum_eq]
  exact DFinsupp.sum_zero_index

@[simp]
theorem sum_zero {ι : Type*} {β : ι → Type*} [∀ i, AddCommMonoid (β i)]
    {M : Type*} [AddCommMonoid M] (x : Π₀ i, β i) :
    sum x (fun _ _ ↦ (0 : M)) = 0 := by
  classical
  rw [sum_eq]
  exact DFinsupp.sum_zero

theorem sum_single_index {ι : Type*} {β : ι → Type*} [∀ i, Zero (β i)] [DecidableEq ι]
    {M : Type*} [AddCommMonoid M] (i : ι) (x : β i) (f : ∀ i, β i → M)
    (h : f i 0 = 0) : sum (DFinsupp.single i x) f = f i x := by
  classical
  rw [sum_eq]
  exact DFinsupp.sum_single_index h

theorem sum_add_index {ι : Type*} {β : ι → Type*} [∀ i, AddCommMonoid (β i)]
    {M : Type*} [AddCommMonoid M] (x y : Π₀ i, β i) (f : ∀ i, β i → M)
    (hzero : ∀ i, f i 0 = 0) (hadd : ∀ i a b, f i (a + b) = f i a + f i b) :
    sum (x + y) f = sum x f + sum y f := by
  classical
  simp only [sum_eq]
  exact DFinsupp.sum_add_index hzero hadd

theorem sum_add {ι : Type*} {β : ι → Type*} [∀ i, AddCommMonoid (β i)]
    {M : Type*} [AddCommMonoid M] (x : Π₀ i, β i) (f g : ∀ i, β i → M) :
    sum x (fun i a ↦ f i a + g i a) = sum x f + sum x g := by
  classical
  simp only [sum_eq]
  exact DFinsupp.sum_add

/-- Multiply two base coefficients and reindex the result into the coefficient degree belonging
to the sum of their exponents. -/
def coefficientMul (A : NonnegGradedAlgebra.{u, v} R) (d m n i j : ℕ)
    (hi : i * d ≤ m) (hj : j * d ≤ n)
    (x : A.piece (m - i * d)) (y : A.piece (n - j * d)) :
    A.piece ((m + n) - (i + j) * d) :=
  cast (congrArg A.piece <|
    (tsub_add_eq_add_tsub hi).trans <|
      (congrArg (fun q ↦ q - i * d) (add_tsub_assoc_of_le hj m).symm).trans <|
        (tsub_tsub (m + n) (j * d) (i * d)).trans <|
          congrArg (fun q ↦ (m + n) - q) <|
            (Nat.add_comm (j * d) (i * d)).trans (Nat.add_mul i j d).symm) <|
    (GradedMonoid.GMul.mul x y)

theorem coefficientMulDegree (d m n i j : ℕ) (hi : i * d ≤ m) (hj : j * d ≤ n) :
    (m - i * d) + (n - j * d) = (m + n) - (i + j) * d :=
  (tsub_add_eq_add_tsub hi).trans <|
    (congrArg (fun q ↦ q - i * d) (add_tsub_assoc_of_le hj m).symm).trans <|
      (tsub_tsub (m + n) (j * d) (i * d)).trans <|
        congrArg (fun q ↦ (m + n) - q) <|
          (Nat.add_comm (j * d) (i * d)).trans (Nat.add_mul i j d).symm

theorem coefficientMul_zero_right (A : NonnegGradedAlgebra.{u, v} R) (d m n i j : ℕ)
    (hi : i * d ≤ m) (hj : j * d ≤ n) (x : A.piece (m - i * d)) :
    coefficientMul A d m n i j hi hj x 0 = 0 := by
  unfold coefficientMul
  rw [DirectSum.GNonUnitalNonAssocSemiring.mul_zero]
  exact cast_zero A (coefficientMulDegree d m n i j hi hj)

theorem coefficientMul_zero_left (A : NonnegGradedAlgebra.{u, v} R) (d m n i j : ℕ)
    (hi : i * d ≤ m) (hj : j * d ≤ n) (y : A.piece (n - j * d)) :
    coefficientMul A d m n i j hi hj 0 y = 0 := by
  unfold coefficientMul
  rw [DirectSum.GNonUnitalNonAssocSemiring.zero_mul]
  exact cast_zero A (coefficientMulDegree d m n i j hi hj)

theorem coefficientMul_add_right (A : NonnegGradedAlgebra.{u, v} R) (d m n i j : ℕ)
    (hi : i * d ≤ m) (hj : j * d ≤ n)
    (x : A.piece (m - i * d)) (y z : A.piece (n - j * d)) :
    coefficientMul A d m n i j hi hj x (y + z) =
      coefficientMul A d m n i j hi hj x y + coefficientMul A d m n i j hi hj x z := by
  unfold coefficientMul
  rw [DirectSum.GNonUnitalNonAssocSemiring.mul_add]
  exact cast_add A (coefficientMulDegree d m n i j hi hj) _ _

theorem coefficientMul_add_left (A : NonnegGradedAlgebra.{u, v} R) (d m n i j : ℕ)
    (hi : i * d ≤ m) (hj : j * d ≤ n)
    (x y : A.piece (m - i * d)) (z : A.piece (n - j * d)) :
    coefficientMul A d m n i j hi hj (x + y) z =
      coefficientMul A d m n i j hi hj x z + coefficientMul A d m n i j hi hj y z := by
  unfold coefficientMul
  rw [DirectSum.GNonUnitalNonAssocSemiring.add_mul]
  exact cast_add A (coefficientMulDegree d m n i j hi hj) _ _

/-- Evaluate one coefficient monomial against a degree-preserving base map and a chosen family of
target monomials. -/
def evalMonomial {ι : Type*} (exponent : ι → ℕ)
    (A B : NonnegGradedAlgebra.{u, v} R) (d m : ℕ) (g : NonnegGradedAlgebra.Hom A B)
    (power : ∀ i, B.piece (exponent i * d))
    (i : {i : ι // exponent i * d ≤ m}) (a : A.piece (m - exponent i * d)) : B.piece m :=
  cast (congrArg B.piece (Nat.sub_add_cancel i.property))
    (GradedMonoid.GMul.mul (g.map (m - exponent i * d) a) (power i))

/-- Evaluate a finitely supported homogeneous coefficient family in a target graded algebra. -/
def eval {ι : Type*} (exponent : ι → ℕ)
    (A B : NonnegGradedAlgebra.{u, v} R) (d m : ℕ) (g : NonnegGradedAlgebra.Hom A B)
    (power : ∀ i, B.piece (exponent i * d))
    (z : ShiftSum A (fun i ↦ exponent i * d) m) : B.piece m :=
  sum z fun i a ↦ evalMonomial exponent A B d m g power i a

theorem eval_eq_lsum {ι : Type*} (exponent : ι → ℕ)
    (A B : NonnegGradedAlgebra.{u, v} R) (d m : ℕ) (g : NonnegGradedAlgebra.Hom A B)
    (power : ∀ i, B.piece (exponent i * d))
    (z : ShiftSum A (fun i ↦ exponent i * d) m) :
    eval exponent A B d m g power z =
      (by classical exact DFinsupp.lsum ℕ (fun i : {i : ι // exponent i * d ≤ m} ↦
        (B.pieceCast (Nat.sub_add_cancel i.property)).comp
          (((DirectSum.gMulLHom R B.piece).flip (power i)).comp
            (g.map (m - exponent i * d)))) z) := by
  classical
  rw [eval, sum_eq, DFinsupp.lsum_apply_apply, DFinsupp.sumAddHom_apply]
  congr 1
  funext i a
  simp only [evalMonomial, LinearMap.toAddMonoidHom_coe,
    LinearMap.comp_apply, LinearMap.flip_apply, DirectSum.gMulLHom_apply_apply,
    pieceCast_apply]

/-- Homogeneous coefficient evaluation preserves addition. -/
theorem eval_add {ι : Type*} (exponent : ι → ℕ)
    (A B : NonnegGradedAlgebra.{u, v} R) (d m : ℕ) (g : NonnegGradedAlgebra.Hom A B)
    (power : ∀ i, B.piece (exponent i * d))
    (x y : ShiftSum A (fun i ↦ exponent i * d) m) :
    eval exponent A B d m g power (x + y) =
      eval exponent A B d m g power x + eval exponent A B d m g power y := by
  simp only [eval_eq_lsum, map_add]

/-- Homogeneous coefficient evaluation preserves scalar multiplication. -/
theorem eval_smul {ι : Type*} (exponent : ι → ℕ)
    (A B : NonnegGradedAlgebra.{u, v} R) (d m : ℕ) (g : NonnegGradedAlgebra.Hom A B)
    (power : ∀ i, B.piece (exponent i * d)) (r : R)
    (x : ShiftSum A (fun i ↦ exponent i * d) m) :
    eval exponent A B d m g power (r • x) = r • eval exponent A B d m g power x := by
  simp only [eval_eq_lsum, map_smul]

/-- The degreewise linear map obtained by evaluating a homogeneous coefficient family. -/
def evalMap {ι : Type*} (exponent : ι → ℕ)
    (A B : NonnegGradedAlgebra.{u, v} R) (d m : ℕ) (g : NonnegGradedAlgebra.Hom A B)
    (power : ∀ i, B.piece (exponent i * d)) :
    ShiftSum A (fun i ↦ exponent i * d) m →ₗ[R] B.piece m where
  toFun := eval exponent A B d m g power
  map_add' := eval_add exponent A B d m g power
  map_smul' := eval_smul exponent A B d m g power

end Implementation

namespace Odd

variable (A : NonnegGradedAlgebra.{u, v} R) (d : ℕ)

/-- The exponent-zero index in a homogeneous odd-variable coefficient piece. -/
def zeroIndex (m : ℕ) : {i : Fin 2 // (i : ℕ) * d ≤ m} :=
  ⟨(0 : Fin 2),
    Eq.mp (congrArg (fun q ↦ q ≤ m) (Nat.zero_mul d).symm) (Nat.zero_le m)⟩

/-- The exponent-one index in the degree of an odd variable. -/
def oneIndexOfLE {m : ℕ} (h : d ≤ m) : {i : Fin 2 // (i : ℕ) * d ≤ m} :=
  ⟨(1 : Fin 2),
    Eq.mp (congrArg (fun q ↦ q ≤ m) (Nat.one_mul d).symm) h⟩

/-- The exponent-one index in the degree of an odd variable. -/
def oneIndex : {i : Fin 2 // (i : ℕ) * d ≤ d} :=
  oneIndexOfLE d (le_refl d)

/-- Addition of odd exponents when their sum is still below two. -/
def addIndex {m n : ℕ} (i : {i : Fin 2 // (i : ℕ) * d ≤ m})
    (j : {j : Fin 2 // (j : ℕ) * d ≤ n})
    (hij : (i : ℕ) + (j : ℕ) < 2) :
    {k : Fin 2 // (k : ℕ) * d ≤ m + n} :=
  ⟨⟨(i : ℕ) + (j : ℕ), hij⟩,
    Eq.mp (congrArg (fun q ↦ q ≤ m + n) (Nat.add_mul i j d).symm)
      (Nat.add_le_add i.property j.property)⟩

/-- The Koszul sign produced by moving the left variable monomial past the right coefficient. -/
def koszulSign {n : ℕ} (i : Fin 2) (j : {j : Fin 2 // (j : ℕ) * d ≤ n}) : R :=
  (-1 : R) ^ ((i : ℕ) * d * (n - (j : ℕ) * d))

/-- Multiplication of two homogeneous odd-variable monomials.  A product containing `T * T`
is explicitly zero; all other products carry the Koszul sign forced by the coefficient degree. -/
def monomialMul {m n : ℕ}
    (i : {i : Fin 2 // (i : ℕ) * d ≤ m}) (x : A.piece (m - (i : ℕ) * d))
    (j : {j : Fin 2 // (j : ℕ) * d ≤ n}) (y : A.piece (n - (j : ℕ) * d)) :
    Piece A d (m + n) :=
  if hij : (i : ℕ) + (j : ℕ) < 2 then
    DFinsupp.single (addIndex d i j hij)
      (koszulSign (R := R) d i j •
        Implementation.coefficientMul A d m n i j i.property j.property x y)
  else 0

/-- Explicit heterogeneous multiplication on the odd-variable coefficient pieces. -/
def mul {m n : ℕ} (x : Piece A d m) (y : Piece A d n) : Piece A d (m + n) :=
  Implementation.sum x fun i xi ↦
    Implementation.sum y fun j yj ↦ monomialMul A d i xi j yj

theorem monomialMul_zero_right {m n : ℕ}
    (i : {i : Fin 2 // (i : ℕ) * d ≤ m}) (x : A.piece (m - (i : ℕ) * d))
    (j : {j : Fin 2 // (j : ℕ) * d ≤ n}) : monomialMul A d i x j 0 = 0 := by
  unfold monomialMul
  split_ifs
  · rw [Implementation.coefficientMul_zero_right]
    rw [smul_zero]
    exact DFinsupp.single_zero _
  · rfl

theorem monomialMul_zero_left {m n : ℕ}
    (i : {i : Fin 2 // (i : ℕ) * d ≤ m})
    (j : {j : Fin 2 // (j : ℕ) * d ≤ n}) (y : A.piece (n - (j : ℕ) * d)) :
    monomialMul A d i 0 j y = 0 := by
  unfold monomialMul
  split_ifs
  · rw [Implementation.coefficientMul_zero_left]
    rw [smul_zero]
    exact DFinsupp.single_zero _
  · rfl

theorem monomialMul_add_right {m n : ℕ}
    (i : {i : Fin 2 // (i : ℕ) * d ≤ m}) (x : A.piece (m - (i : ℕ) * d))
    (j : {j : Fin 2 // (j : ℕ) * d ≤ n}) (y z : A.piece (n - (j : ℕ) * d)) :
    monomialMul A d i x j (y + z) = monomialMul A d i x j y + monomialMul A d i x j z := by
  unfold monomialMul
  split_ifs
  · rw [Implementation.coefficientMul_add_right]
    rw [smul_add]
    exact DFinsupp.single_add _ _ _
  · exact (add_zero _).symm

theorem monomialMul_add_left {m n : ℕ}
    (i : {i : Fin 2 // (i : ℕ) * d ≤ m}) (x y : A.piece (m - (i : ℕ) * d))
    (j : {j : Fin 2 // (j : ℕ) * d ≤ n}) (z : A.piece (n - (j : ℕ) * d)) :
    monomialMul A d i (x + y) j z = monomialMul A d i x j z + monomialMul A d i y j z := by
  unfold monomialMul
  split_ifs
  · rw [Implementation.coefficientMul_add_left]
    rw [smul_add]
    exact DFinsupp.single_add _ _ _
  · exact (add_zero _).symm

/-- Multiplication of two one-term odd-variable representatives is `monomialMul`. -/
@[simp]
theorem single_mul_single {m n : ℕ}
    (i : {i : Fin 2 // (i : ℕ) * d ≤ m}) (x : A.piece (m - (i : ℕ) * d))
    (j : {j : Fin 2 // (j : ℕ) * d ≤ n}) (y : A.piece (n - (j : ℕ) * d)) :
    mul A d (DFinsupp.single i x) (DFinsupp.single j y) = monomialMul A d i x j y := by
  unfold mul
  rw [Implementation.sum_single_index]
  · change Implementation.sum (DFinsupp.single j y) (fun j yj ↦ monomialMul A d i x j yj) =
      monomialMul A d i x j y
    exact Implementation.sum_single_index
      (β := fun j : {j : Fin 2 // (j : ℕ) * d ≤ n} ↦ A.piece (n - (j : ℕ) * d))
      (M := Piece A d (m + n)) j y (fun j yj ↦ monomialMul A d i x j yj)
      (monomialMul_zero_right A d i x j)
  · change Implementation.sum (DFinsupp.single j y) (fun j yj ↦ monomialMul A d i 0 j yj) = 0
    simp only [monomialMul_zero_left, Implementation.sum_zero]

/-- The homogeneous unit of the odd-variable coefficient model. -/
def one : Piece A d 0 :=
  DFinsupp.single (zeroIndex d 0)
    (cast (congrArg A.piece <|
      (Nat.sub_zero 0).symm.trans <|
        congrArg (fun q ↦ 0 - q) (Nat.zero_mul d).symm) <|
      (GradedMonoid.GOne.one : A.piece 0))

/-- Odd-variable coefficient pieces carry their explicit heterogeneous multiplication. -/
noncomputable instance pieceGMul : GradedMonoid.GMul (Piece A d) where
  mul := mul A d

/-- Odd-variable coefficient pieces carry their explicit homogeneous unit. -/
noncomputable instance pieceGOne : GradedMonoid.GOne (Piece A d) where
  one := one A d

/-- The odd-variable coefficient unit is a left identity. -/
theorem one_mul (x : GradedMonoid (Piece A d)) : 1 * x = x := sorry

/-- The odd-variable coefficient unit is a right identity. -/
theorem mul_one (x : GradedMonoid (Piece A d)) : x * 1 = x := sorry

/-- Explicit odd-variable coefficient multiplication is associative. -/
theorem mul_assoc (x y z : GradedMonoid (Piece A d)) : x * y * z = x * (y * z) := sorry

/-- Odd-variable coefficient pieces form a graded monoid. -/
noncomputable instance pieceGMonoid : GradedMonoid.GMonoid (Piece A d) where
  one_mul := one_mul A d
  mul_one := mul_one A d
  mul_assoc := mul_assoc A d

/-- Multiplication by a zero odd-variable coefficient vanishes on the right. -/
theorem mul_zero {m n : ℕ} (x : Piece A d m) :
    GradedMonoid.GMul.mul x (0 : Piece A d n) = 0 := by
  change mul A d x 0 = 0
  simp only [mul, Implementation.sum_zero_index, Implementation.sum_zero]

/-- Multiplication by a zero odd-variable coefficient vanishes on the left. -/
theorem zero_mul {m n : ℕ} (y : Piece A d n) :
    GradedMonoid.GMul.mul (0 : Piece A d m) y = 0 := by
  change mul A d 0 y = 0
  simp only [mul, Implementation.sum_zero_index]

/-- Odd-variable coefficient multiplication distributes over addition on the right. -/
theorem mul_add {m n : ℕ} (x : Piece A d m) (y z : Piece A d n) :
    GradedMonoid.GMul.mul x (y + z) =
      GradedMonoid.GMul.mul x y + GradedMonoid.GMul.mul x z := by
  change mul A d x (y + z) = mul A d x y + mul A d x z
  unfold mul
  have hsum : ∀ (i : {i : Fin 2 // (i : ℕ) * d ≤ m}) (xi : A.piece (m - (i : ℕ) * d)),
      Implementation.sum (y + z) (fun j yj ↦ monomialMul A d i xi j yj) =
        Implementation.sum y (fun j yj ↦ monomialMul A d i xi j yj) +
          Implementation.sum z (fun j yj ↦ monomialMul A d i xi j yj) := by
    intro i xi
    exact Implementation.sum_add_index y z _ (monomialMul_zero_right A d i xi)
      (fun j a b ↦ monomialMul_add_right A d i xi j a b)
  simp only [hsum, Implementation.sum_add]

/-- Odd-variable coefficient multiplication distributes over addition on the left. -/
theorem add_mul {m n : ℕ} (x y : Piece A d m) (z : Piece A d n) :
    GradedMonoid.GMul.mul (x + y) z =
      GradedMonoid.GMul.mul x z + GradedMonoid.GMul.mul y z := by
  change mul A d (x + y) z = mul A d x z + mul A d y z
  unfold mul
  apply Implementation.sum_add_index
  · change ∀ i, Implementation.sum z (fun j yj ↦ monomialMul A d i 0 j yj) = 0
    intro i
    simp only [monomialMul_zero_left, Implementation.sum_zero]
  · change ∀ i a b, Implementation.sum z (fun j yj ↦ monomialMul A d i (a + b) j yj) =
      Implementation.sum z (fun j yj ↦ monomialMul A d i a j yj) +
        Implementation.sum z (fun j yj ↦ monomialMul A d i b j yj)
    intro i a b
    simp only [monomialMul_add_left, Implementation.sum_add]

/-- Odd-variable coefficient pieces form a graded nonunital nonassociative semiring. -/
noncomputable instance pieceGNonUnitalNonAssocSemiring :
    DirectSum.GNonUnitalNonAssocSemiring (Piece A d) where
  mul_zero := mul_zero A d
  zero_mul := zero_mul A d
  mul_add := mul_add A d
  add_mul := add_mul A d

/-- The natural-number cast into degree zero of the odd-variable model. -/
def natCast (n : ℕ) : Piece A d 0 := n • one A d

/-- The odd-variable natural-number cast sends zero to zero. -/
theorem natCast_zero : natCast A d 0 = 0 := by
  simp [natCast]

/-- The odd-variable natural-number cast preserves successors. -/
theorem natCast_succ (n : ℕ) : natCast A d (n + 1) = natCast A d n + one A d := by
  simp [natCast, add_smul]

/-- Odd-variable coefficient pieces form a graded semiring. -/
noncomputable instance pieceGSemiring : DirectSum.GSemiring (Piece A d) where
  natCast := natCast A d
  natCast_zero := natCast_zero A d
  natCast_succ := natCast_succ A d

/-- The structural scalar map into degree zero of the odd-variable model. -/
def algebraMap : R →+ Piece A d 0 :=
  (LinearMap.toSpanSingleton R (Piece A d 0) (one A d)).toAddMonoidHom

/-- The odd-variable structural scalar map preserves one. -/
theorem algebraMap_one : algebraMap A d 1 = GradedMonoid.GOne.one := by
  change (1 : R) • one A d = one A d
  exact one_smul R _

/-- The odd-variable structural scalar map preserves multiplication. -/
theorem algebraMap_mul (r s : R) :
    GradedMonoid.mk 0 (algebraMap A d (r * s)) =
      GradedMonoid.mk 0 (GradedMonoid.GMul.mul (algebraMap A d r) (algebraMap A d s)) := sorry

/-- Scalars commute with every homogeneous odd-variable coefficient. -/
theorem algebraMap_commutes (r : R) (x : GradedMonoid (Piece A d)) :
    GradedMonoid.mk 0 (algebraMap A d r) * x =
      x * GradedMonoid.mk 0 (algebraMap A d r) := sorry

/-- Scalar multiplication agrees with multiplication by the degree-zero scalar image. -/
theorem algebraMap_smul (r : R) (x : GradedMonoid (Piece A d)) :
    r • x = GradedMonoid.mk 0 (algebraMap A d r) * x := sorry

/-- Odd-variable coefficient pieces inherit their graded `R`-algebra structure. -/
noncomputable instance pieceGAlgebra : DirectSum.GAlgebra R (Piece A d) where
  toFun := algebraMap A d
  map_one := algebraMap_one A d
  map_mul := algebraMap_mul A d
  commutes := algebraMap_commutes A d
  smul_def := algebraMap_smul A d

/-- Odd-degree adjoining multiplication obeys the Koszul commutativity rule. -/
theorem mul_comm (hd : Odd d) (m n : ℕ) (x : Piece A d m) (y : Piece A d n) :
    GradedMonoid.GMul.mul x y =
      cast (congrArg (Piece A d) (Nat.add_comm n m))
        (((-1 : R) ^ (m * n)) • GradedMonoid.GMul.mul y x) := sorry

/-- Odd homogeneous elements square to zero after adjoining an odd variable. -/
theorem sq_eq_zero_of_odd (hd : Odd d) {m : ℕ} (hm : Odd m) (x : Piece A d m) :
    GradedMonoid.GMul.mul x x = 0 := sorry

/-- The strictly graded-commutative law selected by an oddness proof for the adjoined degree. -/
theorem pieceIsStrictlyCommutative (hd : Odd d) :
    DirectSum.Graded.IsStrictlyCommutative R (Piece A d) := by
  exact {
    mul_comm := mul_comm A d hd
    sq_eq_zero_of_odd := sq_eq_zero_of_odd A d hd }

/-- Example 23.6.2 (Adjoining odd variable) (Tag 09PH): the canonical bundled nonnegative
graded algebra obtained by adjoining an exterior variable of positive odd degree `d`. -/
@[stacks 09PH "bundled odd-variable algebra"]
def algebra (hd : Odd d) : NonnegGradedAlgebra.{u, v} R where
  piece := Piece A d
  pieceAddCommGroup := fun _ ↦ inferInstance
  pieceModule := fun _ ↦ inferInstance
  pieceGSemiring := pieceGSemiring A d
  pieceGAlgebra := pieceGAlgebra A d
  pieceIsStrictlyCommutative := pieceIsStrictlyCommutative A d hd

/-- The constant-coefficient representative of a homogeneous base element. -/
def baseCoeff (m : ℕ) (x : A.piece m) : Piece A d m :=
  DFinsupp.single (zeroIndex d m)
    (cast (congrArg A.piece <|
      (Nat.sub_zero m).symm.trans <|
        congrArg (fun q ↦ m - q) (Nat.zero_mul d).symm) x)

/-- Constant-coefficient inclusion preserves addition. -/
theorem baseCoeff_add (m : ℕ) (x y : A.piece m) :
    baseCoeff A d m (x + y) = baseCoeff A d m x + baseCoeff A d m y := by
  unfold baseCoeff
  exact (congrArg (DFinsupp.single (zeroIndex d m))
    (Implementation.cast_add A ((Nat.sub_zero m).symm.trans (congrArg (fun q ↦ m - q) (Nat.zero_mul d).symm)) x y)).trans (DFinsupp.single_add _ _ _)

/-- Constant-coefficient inclusion preserves scalar multiplication. -/
theorem baseCoeff_smul (m : ℕ) (r : R) (x : A.piece m) :
    baseCoeff A d m (r • x) = r • baseCoeff A d m x := by
  unfold baseCoeff
  exact (congrArg (DFinsupp.single (zeroIndex d m))
    (Implementation.cast_smul A ((Nat.sub_zero m).symm.trans (congrArg (fun q ↦ m - q) (Nat.zero_mul d).symm)) r x)).trans (DFinsupp.single_smul r _)

/-- The degreewise linear constant-coefficient inclusion. -/
def baseMap (m : ℕ) : A.piece m →ₗ[R] Piece A d m where
  toFun := baseCoeff A d m
  map_add' := baseCoeff_add A d m
  map_smul' := baseCoeff_smul A d m

/-- The coefficient selected by the exponent-zero index lies in the unshifted base degree. -/
theorem zeroCoefficientDegree (m : ℕ) :
    m - (zeroIndex d m : ℕ) * d = m := by
  simp [zeroIndex]

/-- The coefficient selected by the exponent-one index lies in degree `m - d`. -/
theorem oneCoefficientDegree {m : ℕ} (h : d ≤ m) :
    m - (oneIndexOfLE d h : ℕ) * d = m - d := by
  simp [oneIndexOfLE]

/-- Projection of an odd-variable coefficient family onto its constant coefficient. -/
def baseProjection (m : ℕ) : Piece A d m →ₗ[R] A.piece m :=
  (A.pieceCast <|
    (congrArg (fun q : ℕ ↦ m - q) (Nat.zero_mul d)).trans (Nat.sub_zero m)).comp <|
      DFinsupp.lapply (zeroIndex d m)

/-- Projecting a constant coefficient recovers the original homogeneous element. -/
theorem baseProjection_baseMap (m : ℕ) (x : A.piece m) :
    baseProjection A d m (baseMap A d m x) = x := by
  change (A.pieceCast ((congrArg (fun q : ℕ ↦ m - q) (Nat.zero_mul d)).trans
    (Nat.sub_zero m))) (baseCoeff A d m x (zeroIndex d m)) = x
  rw [Implementation.pieceCast_apply]
  unfold baseCoeff
  rw [DFinsupp.single_eq_same]
  exact (cast_cast (congrArg A.piece ((Nat.sub_zero m).symm.trans (congrArg (fun q ↦ m - q) (Nat.zero_mul d).symm)))
    (congrArg A.piece ((Nat.sub_zero m).symm.trans (congrArg (fun q ↦ m - q) (Nat.zero_mul d).symm)).symm) x).trans (cast_eq _ x)

/-- Below the variable degree, a homogeneous odd-variable coefficient family has only its
constant coefficient. -/
theorem baseMap_baseProjection_of_lt {m : ℕ} (h : m < d) (x : Piece A d m) :
    baseMap A d m (baseProjection A d m x) = x := by
  apply DFinsupp.ext
  intro i
  have hi : i = zeroIndex d m := by
    apply Subtype.ext
    apply Fin.ext
    have hlt := (i : Fin 2).isLt
    have hcases : (i : ℕ) = 0 ∨ (i : ℕ) = 1 := by omega
    rcases hcases with hi | hi
    · exact hi
    · have hle : d ≤ m := by simpa only [hi, Nat.one_mul] using i.property
      omega
  subst i
  change DFinsupp.single (β := fun i : {i : Fin 2 // (i : ℕ) * d ≤ m} ↦ A.piece (m - (i : ℕ) * d)) (zeroIndex d m)
    (cast (congrArg A.piece (zeroCoefficientDegree d m).symm)
      (A.pieceCast (zeroCoefficientDegree d m) (x (zeroIndex d m)))) (zeroIndex d m) = _
  rw [DFinsupp.single_eq_same, Implementation.pieceCast_apply]
  exact Implementation.cast_roundtrip _ _ _

/-- Below the variable degree, the odd-variable homogeneous piece is canonically the
corresponding homogeneous piece of the base algebra. -/
@[stacks 09PH "odd-variable low-degree coefficient identification"]
def baseEquivOfLT {m : ℕ} (h : m < d) : Piece A d m ≃ₗ[R] A.piece m where
  toLinearMap := baseProjection A d m
  invFun := baseMap A d m
  left_inv := baseMap_baseProjection_of_lt A d h
  right_inv := baseProjection_baseMap A d m

/-- Projection of an odd-variable coefficient family onto its variable coefficient. -/
def variableProjection {m : ℕ} (h : d ≤ m) : Piece A d m →ₗ[R] A.piece (m - d) :=
  (A.pieceCast <| congrArg (fun q : ℕ ↦ m - q) (Nat.one_mul d)).comp <|
    DFinsupp.lapply (oneIndexOfLE d h)

/-- Insert a base coefficient as the coefficient of the odd variable in total degree `m`. -/
def variableMap {m : ℕ} (h : d ≤ m) : A.piece (m - d) →ₗ[R] Piece A d m :=
  (DFinsupp.lsingle (oneIndexOfLE d h)).comp <|
    A.pieceCast (congrArg (fun q : ℕ ↦ m - q) (Nat.one_mul d)).symm

theorem zeroIndex_ne_oneIndexOfLE {m : ℕ} (h : d ≤ m) :
    zeroIndex d m ≠ oneIndexOfLE d h := by
  intro e
  have he := congrArg (fun i : {i : Fin 2 // (i : ℕ) * d ≤ m} ↦ (i : ℕ)) e
  simp only [zeroIndex, oneIndexOfLE, Fin.val_zero, Fin.val_one] at he
  exact Nat.zero_ne_one he

theorem baseMap_apply_baseProjection (m : ℕ) (x : Piece A d m) :
    baseMap A d m (baseProjection A d m x) (zeroIndex d m) = x (zeroIndex d m) := by
  change DFinsupp.single (β := fun i : {i : Fin 2 // (i : ℕ) * d ≤ m} ↦ A.piece (m - (i : ℕ) * d)) (zeroIndex d m)
    (cast (congrArg A.piece (zeroCoefficientDegree d m).symm)
      (A.pieceCast (zeroCoefficientDegree d m) (x (zeroIndex d m)))) (zeroIndex d m) = _
  rw [DFinsupp.single_eq_same, Implementation.pieceCast_apply]
  exact Implementation.cast_roundtrip _ _ _

theorem variableMap_apply_variableProjection {m : ℕ} (h : d ≤ m) (x : Piece A d m) :
    variableMap A d h (variableProjection A d h x) (oneIndexOfLE d h) =
      x (oneIndexOfLE d h) := by
  change DFinsupp.single (β := fun i : {i : Fin 2 // (i : ℕ) * d ≤ m} ↦ A.piece (m - (i : ℕ) * d)) (oneIndexOfLE d h)
    (A.pieceCast (oneCoefficientDegree d h).symm
      (A.pieceCast (oneCoefficientDegree d h) (x (oneIndexOfLE d h)))) (oneIndexOfLE d h) = _
  rw [DFinsupp.single_eq_same, Implementation.pieceCast_apply, Implementation.pieceCast_apply]
  exact Implementation.cast_roundtrip _ _ _

theorem baseProjection_variableMap {m : ℕ} (h : d ≤ m) (x : A.piece (m - d)) :
    baseProjection A d m (variableMap A d h x) = 0 := by
  change A.pieceCast (zeroCoefficientDegree d m)
    (DFinsupp.single (β := fun i : {i : Fin 2 // (i : ℕ) * d ≤ m} ↦ A.piece (m - (i : ℕ) * d)) (oneIndexOfLE d h)
      (A.pieceCast (oneCoefficientDegree d h).symm x) (zeroIndex d m)) = 0
  rw [DFinsupp.single_eq_of_ne (zeroIndex_ne_oneIndexOfLE d h), map_zero]

theorem variableProjection_baseMap {m : ℕ} (h : d ≤ m) (x : A.piece m) :
    variableProjection A d h (baseMap A d m x) = 0 := by
  change A.pieceCast (oneCoefficientDegree d h)
    (DFinsupp.single (β := fun i : {i : Fin 2 // (i : ℕ) * d ≤ m} ↦ A.piece (m - (i : ℕ) * d)) (zeroIndex d m)
      (cast (congrArg A.piece (zeroCoefficientDegree d m).symm) x) (oneIndexOfLE d h)) = 0
  rw [DFinsupp.single_eq_of_ne (zeroIndex_ne_oneIndexOfLE d h).symm, map_zero]

theorem variableProjection_variableMap {m : ℕ} (h : d ≤ m) (x : A.piece (m - d)) :
    variableProjection A d h (variableMap A d h x) = x := by
  change A.pieceCast (oneCoefficientDegree d h)
    (DFinsupp.single (β := fun i : {i : Fin 2 // (i : ℕ) * d ≤ m} ↦ A.piece (m - (i : ℕ) * d)) (oneIndexOfLE d h)
      (A.pieceCast (oneCoefficientDegree d h).symm x) (oneIndexOfLE d h)) = x
  rw [DFinsupp.single_eq_same, Implementation.pieceCast_apply, Implementation.pieceCast_apply]
  exact Implementation.cast_roundtrip _ _ _

/-- Split an odd-variable coefficient family into its constant and variable coefficients. -/
def split {m : ℕ} (h : d ≤ m) : Piece A d m →ₗ[R] A.piece m × A.piece (m - d) :=
  (baseProjection A d m).prod (variableProjection A d h)

/-- Assemble an odd-variable coefficient family from its constant and variable coefficients. -/
def combine {m : ℕ} (h : d ≤ m) : A.piece m × A.piece (m - d) →ₗ[R] Piece A d m :=
  (baseMap A d m).comp (LinearMap.fst R _ _) +
    (variableMap A d h).comp (LinearMap.snd R _ _)

/-- Splitting after assembling the two coefficients is the identity. -/
theorem split_combine {m : ℕ} (h : d ≤ m)
    (x : A.piece m × A.piece (m - d)) :
    split A d h (combine A d h x) = x := by
  apply Prod.ext
  · change baseProjection A d m (baseMap A d m x.1 + variableMap A d h x.2) = x.1
    rw [map_add, baseProjection_baseMap, baseProjection_variableMap, add_zero]
  · change variableProjection A d h (baseMap A d m x.1 + variableMap A d h x.2) = x.2
    rw [map_add, variableProjection_baseMap, variableProjection_variableMap, zero_add]

/-- Assembling the two projections of a coefficient family recovers that family. -/
theorem combine_split {m : ℕ} (h : d ≤ m) (x : Piece A d m) :
    combine A d h (split A d h x) = x := by
  apply DFinsupp.ext
  intro i
  have hlt := (i : Fin 2).isLt
  have hcases : (i : ℕ) = 0 ∨ (i : ℕ) = 1 := by omega
  rcases hcases with hi | hi
  · have he : i = zeroIndex d m := Subtype.ext (Fin.ext hi)
    subst i
    change (baseMap A d m (baseProjection A d m x) +
      variableMap A d h (variableProjection A d h x)) (zeroIndex d m) = _
    rw [DFinsupp.add_apply, baseMap_apply_baseProjection]
    change x (zeroIndex d m) + DFinsupp.single (β := fun i : {i : Fin 2 // (i : ℕ) * d ≤ m} ↦ A.piece (m - (i : ℕ) * d)) (oneIndexOfLE d h) _ (zeroIndex d m) = _
    rw [DFinsupp.single_eq_of_ne (zeroIndex_ne_oneIndexOfLE d h), add_zero]
  · have he : i = oneIndexOfLE d h := Subtype.ext (Fin.ext hi)
    subst i
    change (baseMap A d m (baseProjection A d m x) +
      variableMap A d h (variableProjection A d h x)) (oneIndexOfLE d h) = _
    rw [DFinsupp.add_apply, variableMap_apply_variableProjection]
    change DFinsupp.single (β := fun i : {i : Fin 2 // (i : ℕ) * d ≤ m} ↦ A.piece (m - (i : ℕ) * d)) (zeroIndex d m) _ (oneIndexOfLE d h) + x (oneIndexOfLE d h) = _
    rw [DFinsupp.single_eq_of_ne (zeroIndex_ne_oneIndexOfLE d h).symm, zero_add]

/-- An odd-variable piece is canonically the product of its constant coefficient and its
variable coefficient whenever the variable degree is at most the total degree. -/
@[stacks 09PH "odd-variable homogeneous coefficient splitting"]
def splitEquiv {m : ℕ} (h : d ≤ m) :
    Piece A d m ≃ₗ[R] A.piece m × A.piece (m - d) where
  toLinearMap := split A d h
  invFun := combine A d h
  left_inv := combine_split A d h
  right_inv := split_combine A d h

/-- Constant coefficients preserve the graded unit. -/
theorem baseMap_one : baseMap A d 0 GradedMonoid.GOne.one = GradedMonoid.GOne.one := by
  rfl

/-- Constant coefficients preserve homogeneous multiplication. -/
theorem baseMap_mul (m n : ℕ) (x : A.piece m) (y : A.piece n) :
    baseMap A d (m + n) (GradedMonoid.GMul.mul x y) =
      GradedMonoid.GMul.mul (baseMap A d m x) (baseMap A d n y) := sorry

/-- The canonical graded-algebra inclusion into an odd-variable extension. -/
def inclusion (hd : Odd d) : A ⟶ algebra A d hd where
  map := baseMap A d
  map_one := baseMap_one A d
  map_mul := baseMap_mul A d

/-- The homogeneous coefficient vector representing the adjoined odd variable. -/
def generator : Piece A d d :=
  DFinsupp.single (oneIndex d)
    (cast (congrArg A.piece <|
      (Nat.sub_self d).symm.trans <|
        congrArg (fun q ↦ d - q) (Nat.one_mul d).symm) <|
      (GradedMonoid.GOne.one : A.piece 0))

/-- The adjoined odd generator squares to zero. -/
@[simp]
theorem generator_sq :
    GradedMonoid.GMul.mul (generator A d) (generator A d) = 0 := by
  change mul A d (generator A d) (generator A d) = 0
  unfold generator
  rw [single_mul_single]
  simp [monomialMul, oneIndex, oneIndexOfLE]

/-- The canonical inclusion is the constant-coefficient formula in every degree. -/
@[simp]
theorem inclusion_apply (hd : Odd d) (m : ℕ) (x : A.piece m) :
    (inclusion A d hd).map m x = baseCoeff A d m x := by
  rfl

/-- Maps out of an odd-variable extension are determined by their restriction to the base and
their value on the adjoined variable. -/
theorem hom_ext (hd : Odd d) {B : NonnegGradedAlgebra.{u, v} R}
    (f g : algebra A d hd ⟶ B) (hbase : inclusion A d hd ≫ f = inclusion A d hd ≫ g)
    (hgenerator : f.map d (generator A d) = g.map d (generator A d)) : f = g := sorry

/-- The exterior powers of a chosen odd homogeneous target element. -/
def powers {B : NonnegGradedAlgebra.{u, v} R} (x : B.piece d) (i : Fin 2) :
    B.piece ((i : ℕ) * d) :=
  cast (congrArg B.piece (Nat.nsmul_eq_mul i d))
    (GradedMonoid.GMonoid.gnpow (i : ℕ) x)

/-- The degreewise evaluation map determined by a base map and the image of the odd variable. -/
def liftMap {B : NonnegGradedAlgebra.{u, v} R} (g : A ⟶ B) (x : B.piece d) (m : ℕ) :
    Piece A d m →ₗ[R] B.piece m :=
  Implementation.evalMap (fun i : Fin 2 ↦ i) A B d m g (powers d x)

/-- Odd-variable evaluation preserves the graded unit. -/
theorem liftMap_one {B : NonnegGradedAlgebra.{u, v} R} (g : A ⟶ B) (x : B.piece d) :
    liftMap A d g x 0 GradedMonoid.GOne.one = GradedMonoid.GOne.one := sorry

/-- Odd-variable evaluation preserves homogeneous multiplication when the adjoined degree is
odd, so the target image of the generator squares to zero. -/
theorem liftMap_mul (hd : Odd d) {B : NonnegGradedAlgebra.{u, v} R}
    (g : A ⟶ B) (x : B.piece d) (m n : ℕ) (a : Piece A d m) (b : Piece A d n) :
    liftMap A d g x (m + n) (GradedMonoid.GMul.mul a b) =
      GradedMonoid.GMul.mul (liftMap A d g x m a) (liftMap A d g x n b) := sorry

/-- The explicit graded-algebra lift determined by a base map and an odd homogeneous element. -/
def lift (hd : Odd d) {B : NonnegGradedAlgebra.{u, v} R} (g : A ⟶ B) (x : B.piece d) :
    algebra A d hd ⟶ B where
  map := liftMap A d g x
  map_one := liftMap_one A d g x
  map_mul := liftMap_mul A d hd g x

/-- The explicit odd-variable lift restricts to the prescribed base map. -/
@[simp]
theorem lift_base (hd : Odd d) {B : NonnegGradedAlgebra.{u, v} R}
    (g : A ⟶ B) (x : B.piece d) : inclusion A d hd ≫ lift A d hd g x = g := sorry

/-- The explicit odd-variable lift sends the generator to the prescribed homogeneous element. -/
@[simp]
theorem lift_generator (hd : Odd d) {B : NonnegGradedAlgebra.{u, v} R}
    (g : A ⟶ B) (x : B.piece d) :
    (lift A d hd g x).map d (generator A d) = x := sorry

/-- Every morphism out of an odd-variable extension is the lift of its base restriction and its
value on the adjoined generator. -/
theorem hom_eq_lift (hd : Odd d) {B : NonnegGradedAlgebra.{u, v} R}
    (f : algebra A d hd ⟶ B) :
    f = lift A d hd (inclusion A d hd ≫ f) (f.map d (generator A d)) := by
  apply hom_ext A d hd
  · show inclusion A d hd ≫ f = inclusion A d hd ≫
      lift A d hd (inclusion A d hd ≫ f) (f.map d (generator A d))
    rw [lift_base]
  · show f.map d (generator A d) =
      (lift A d hd (inclusion A d hd ≫ f) (f.map d (generator A d))).map d (generator A d)
    rw [lift_generator]

/-- Postcomposition of an odd-variable lift acts on its base map and generator value. -/
@[simp]
theorem lift_comp (hd : Odd d) {B C : NonnegGradedAlgebra.{u, v} R}
    (g : A ⟶ B) (x : B.piece d) (f : B ⟶ C) :
    lift A d hd g x ≫ f = lift A d hd (g ≫ f) (f.map d x) := by
  apply hom_ext A d hd
  · show inclusion A d hd ≫ (lift A d hd g x ≫ f) =
      inclusion A d hd ≫ lift A d hd (g ≫ f) (f.map d x)
    rw [← Category.assoc, lift_base, lift_base]
  · show (lift A d hd g x ≫ f).map d (generator A d) =
      (lift A d hd (g ≫ f) (f.map d x)).map d (generator A d)
    change f.map d ((lift A d hd g x).map d (generator A d)) = _
    rw [lift_generator, lift_generator]

/-- A morphism from the odd-variable extension has the prescribed base restriction and generator
value. -/
def IsLift (hd : Odd d) {B : NonnegGradedAlgebra.{u, v} R}
    (g : A ⟶ B) (x : B.piece d) (f : algebra A d hd ⟶ B) : Prop :=
  inclusion A d hd ≫ f = g ∧ f.map d (generator A d) = x

/-- The explicit odd-variable lift satisfies its universal specification. -/
theorem lift_isLift (hd : Odd d) {B : NonnegGradedAlgebra.{u, v} R}
    (g : A ⟶ B) (x : B.piece d) : IsLift A d hd g x (lift A d hd g x) := by
  exact ⟨lift_base A d hd g x, lift_generator A d hd g x⟩

/-- Every morphism satisfying the odd-variable universal specification is the explicit lift. -/
theorem lift_unique (hd : Odd d) {B : NonnegGradedAlgebra.{u, v} R}
    (g : A ⟶ B) (x : B.piece d) (f : algebra A d hd ⟶ B)
    (hf : IsLift A d hd g x f) : f = lift A d hd g x := by
  apply hom_ext A d hd
  · show inclusion A d hd ≫ f = inclusion A d hd ≫ lift A d hd g x
    rw [lift_base]
    exact hf.1
  · show f.map d (generator A d) = (lift A d hd g x).map d (generator A d)
    rw [lift_generator]
    exact hf.2

/-- A base map and a degree-`d` target element determine a unique odd-variable lift. -/
theorem existsUnique_lift (hd : Odd d) {B : NonnegGradedAlgebra.{u, v} R}
    (g : A ⟶ B) (x : B.piece d) :
    ∃! f : algebra A d hd ⟶ B, IsLift A d hd g x f := by
  exact ⟨lift A d hd g x, lift_isLift A d hd g x, fun f hf ↦
    lift_unique A d hd g x f hf⟩

end Odd

namespace Even

variable (A : NonnegGradedAlgebra.{u, v} R) (d : ℕ)

/-- The exponent-zero index in a homogeneous even-variable coefficient piece. -/
def zeroIndex (m : ℕ) : {i : ℕ // i * d ≤ m} :=
  ⟨0, Eq.mp (congrArg (fun q ↦ q ≤ m) (Nat.zero_mul d).symm) (Nat.zero_le m)⟩

/-- The exponent-one index in the degree of an even variable. -/
def oneIndex : {i : ℕ // i * d ≤ d} :=
  ⟨1, Eq.mp (congrArg (fun q ↦ q ≤ d) (Nat.one_mul d).symm) (le_refl d)⟩

/-- Addition of exponent indices in bounded even-variable coefficient pieces. -/
def addIndex {m n : ℕ} (i : {i : ℕ // i * d ≤ m}) (j : {j : ℕ // j * d ≤ n}) :
    {k : ℕ // k * d ≤ m + n} :=
  ⟨i + j, Eq.mp (congrArg (fun q ↦ q ≤ m + n) (Nat.add_mul i j d).symm)
    (Nat.add_le_add i.property j.property)⟩

/-- Multiplication of two homogeneous divided monomials, with coefficient
`Nat.choose (i + j) i`. -/
def monomialMul {m n : ℕ} (i : {i : ℕ // i * d ≤ m}) (x : A.piece (m - i * d))
    (j : {j : ℕ // j * d ≤ n}) (y : A.piece (n - j * d)) : Piece A d (m + n) :=
  DFinsupp.single (addIndex d i j)
    (Nat.choose (i + j) i •
      Implementation.coefficientMul A d m n i j i.property j.property x y)

/-- Explicit heterogeneous convolution on the even-variable divided-monomial pieces. -/
def pieceMul {m n : ℕ} (x : Piece A d m) (y : Piece A d n) : Piece A d (m + n) :=
  Implementation.sum x fun i xi ↦
    Implementation.sum y fun j yj ↦ monomialMul A d i xi j yj

theorem monomialMul_zero_right {m n : ℕ}
    (i : {i : ℕ // i * d ≤ m}) (x : A.piece (m - i * d))
    (j : {j : ℕ // j * d ≤ n}) : monomialMul A d i x j 0 = 0 := by
  unfold monomialMul
  rw [Implementation.coefficientMul_zero_right]
  rw [smul_zero]
  exact DFinsupp.single_zero _

theorem monomialMul_zero_left {m n : ℕ}
    (i : {i : ℕ // i * d ≤ m})
    (j : {j : ℕ // j * d ≤ n}) (y : A.piece (n - j * d)) :
    monomialMul A d i 0 j y = 0 := by
  unfold monomialMul
  rw [Implementation.coefficientMul_zero_left]
  rw [smul_zero]
  exact DFinsupp.single_zero _

theorem monomialMul_add_right {m n : ℕ}
    (i : {i : ℕ // i * d ≤ m}) (x : A.piece (m - i * d))
    (j : {j : ℕ // j * d ≤ n}) (y z : A.piece (n - j * d)) :
    monomialMul A d i x j (y + z) = monomialMul A d i x j y + monomialMul A d i x j z := by
  unfold monomialMul
  rw [Implementation.coefficientMul_add_right]
  rw [smul_add]
  exact DFinsupp.single_add _ _ _

theorem monomialMul_add_left {m n : ℕ}
    (i : {i : ℕ // i * d ≤ m}) (x y : A.piece (m - i * d))
    (j : {j : ℕ // j * d ≤ n}) (z : A.piece (n - j * d)) :
    monomialMul A d i (x + y) j z = monomialMul A d i x j z + monomialMul A d i y j z := by
  unfold monomialMul
  rw [Implementation.coefficientMul_add_left]
  rw [smul_add]
  exact DFinsupp.single_add _ _ _

/-- Multiplication of two one-term even-variable representatives is `monomialMul`. -/
@[simp]
theorem single_mul_single {m n : ℕ} (i : {i : ℕ // i * d ≤ m})
    (x : A.piece (m - i * d)) (j : {j : ℕ // j * d ≤ n})
    (y : A.piece (n - j * d)) :
    pieceMul A d (DFinsupp.single i x) (DFinsupp.single j y) =
      monomialMul A d i x j y := by
  unfold pieceMul
  rw [Implementation.sum_single_index]
  · change Implementation.sum (DFinsupp.single j y) (fun j yj ↦ monomialMul A d i x j yj) =
      monomialMul A d i x j y
    exact Implementation.sum_single_index
      (β := fun j : {j : ℕ // j * d ≤ n} ↦ A.piece (n - (j : ℕ) * d))
      (M := Piece A d (m + n)) j y (fun j yj ↦ monomialMul A d i x j yj)
      (monomialMul_zero_right A d i x j)
  · change Implementation.sum (DFinsupp.single j y) (fun j yj ↦ monomialMul A d i 0 j yj) = 0
    simp only [monomialMul_zero_left, Implementation.sum_zero]

/-- The homogeneous unit of the even-variable divided-monomial model. -/
def pieceOne : Piece A d 0 :=
  DFinsupp.single (zeroIndex d 0)
    (cast (congrArg A.piece <|
      (Nat.sub_zero 0).symm.trans <|
        congrArg (fun q ↦ 0 - q) (Nat.zero_mul d).symm) <|
      (GradedMonoid.GOne.one : A.piece 0))

/-- Even-variable coefficient pieces carry their explicit heterogeneous multiplication. -/
noncomputable instance pieceGMul : GradedMonoid.GMul (Piece A d) where
  mul := pieceMul A d

/-- Even-variable coefficient pieces carry their explicit homogeneous unit. -/
noncomputable instance pieceGOne : GradedMonoid.GOne (Piece A d) where
  one := pieceOne A d

/-- The even-variable coefficient unit is a left identity. -/
theorem one_mul (x : GradedMonoid (Piece A d)) : 1 * x = x := sorry

/-- The even-variable coefficient unit is a right identity. -/
theorem mul_one (x : GradedMonoid (Piece A d)) : x * 1 = x := sorry

/-- Explicit even-variable coefficient multiplication is associative. -/
theorem mul_assoc (x y z : GradedMonoid (Piece A d)) : x * y * z = x * (y * z) := sorry

/-- Even-variable coefficient pieces form a graded monoid. -/
noncomputable instance pieceGMonoid : GradedMonoid.GMonoid (Piece A d) where
  one_mul := one_mul A d
  mul_one := mul_one A d
  mul_assoc := mul_assoc A d

/-- Multiplication by a zero even-variable coefficient vanishes on the right. -/
theorem mul_zero {m n : ℕ} (x : Piece A d m) :
    GradedMonoid.GMul.mul x (0 : Piece A d n) = 0 := by
  change pieceMul A d x 0 = 0
  simp only [pieceMul, Implementation.sum_zero_index, Implementation.sum_zero]

/-- Multiplication by a zero even-variable coefficient vanishes on the left. -/
theorem zero_mul {m n : ℕ} (y : Piece A d n) :
    GradedMonoid.GMul.mul (0 : Piece A d m) y = 0 := by
  change pieceMul A d 0 y = 0
  simp only [pieceMul, Implementation.sum_zero_index]

/-- Even-variable coefficient multiplication distributes over addition on the right. -/
theorem mul_add {m n : ℕ} (x : Piece A d m) (y z : Piece A d n) :
    GradedMonoid.GMul.mul x (y + z) =
      GradedMonoid.GMul.mul x y + GradedMonoid.GMul.mul x z := by
  change pieceMul A d x (y + z) = pieceMul A d x y + pieceMul A d x z
  unfold pieceMul
  have hsum : ∀ (i : {i : ℕ // i * d ≤ m}) (xi : A.piece (m - (i : ℕ) * d)),
      Implementation.sum (y + z) (fun j yj ↦ monomialMul A d i xi j yj) =
        Implementation.sum y (fun j yj ↦ monomialMul A d i xi j yj) +
          Implementation.sum z (fun j yj ↦ monomialMul A d i xi j yj) := by
    intro i xi
    exact Implementation.sum_add_index y z _ (monomialMul_zero_right A d i xi)
      (fun j a b ↦ monomialMul_add_right A d i xi j a b)
  simp only [hsum, Implementation.sum_add]

/-- Even-variable coefficient multiplication distributes over addition on the left. -/
theorem add_mul {m n : ℕ} (x y : Piece A d m) (z : Piece A d n) :
    GradedMonoid.GMul.mul (x + y) z =
      GradedMonoid.GMul.mul x z + GradedMonoid.GMul.mul y z := by
  change pieceMul A d (x + y) z = pieceMul A d x z + pieceMul A d y z
  unfold pieceMul
  apply Implementation.sum_add_index
  · change ∀ i, Implementation.sum z (fun j yj ↦ monomialMul A d i 0 j yj) = 0
    intro i
    simp only [monomialMul_zero_left, Implementation.sum_zero]
  · change ∀ i a b, Implementation.sum z (fun j yj ↦ monomialMul A d i (a + b) j yj) =
      Implementation.sum z (fun j yj ↦ monomialMul A d i a j yj) +
        Implementation.sum z (fun j yj ↦ monomialMul A d i b j yj)
    intro i a b
    simp only [monomialMul_add_left, Implementation.sum_add]

/-- Even-variable coefficient pieces form a graded nonunital nonassociative semiring. -/
noncomputable instance pieceGNonUnitalNonAssocSemiring :
    DirectSum.GNonUnitalNonAssocSemiring (Piece A d) where
  mul_zero := mul_zero A d
  zero_mul := zero_mul A d
  mul_add := mul_add A d
  add_mul := add_mul A d

/-- The natural-number cast into degree zero of the even-variable model. -/
def natCast (n : ℕ) : Piece A d 0 := n • pieceOne A d

/-- The even-variable natural-number cast sends zero to zero. -/
theorem natCast_zero : natCast A d 0 = 0 := by
  simp [natCast]

/-- The even-variable natural-number cast preserves successors. -/
theorem natCast_succ (n : ℕ) :
    natCast A d (n + 1) = natCast A d n + pieceOne A d := by
  simp [natCast, add_smul]

/-- Even-variable coefficient pieces form a graded semiring. -/
noncomputable instance pieceGSemiring : DirectSum.GSemiring (Piece A d) where
  natCast := natCast A d
  natCast_zero := natCast_zero A d
  natCast_succ := natCast_succ A d

/-- The structural scalar map into degree zero of the even-variable model. -/
def algebraMap : R →+ Piece A d 0 :=
  (LinearMap.toSpanSingleton R (Piece A d 0) (pieceOne A d)).toAddMonoidHom

/-- The even-variable structural scalar map preserves one. -/
theorem algebraMap_one : algebraMap A d 1 = GradedMonoid.GOne.one := by
  change (1 : R) • pieceOne A d = pieceOne A d
  exact one_smul R _

/-- The even-variable structural scalar map preserves multiplication. -/
theorem algebraMap_mul (r s : R) :
    GradedMonoid.mk 0 (algebraMap A d (r * s)) =
      GradedMonoid.mk 0 (GradedMonoid.GMul.mul (algebraMap A d r) (algebraMap A d s)) := sorry

/-- Scalars commute with every homogeneous even-variable coefficient. -/
theorem algebraMap_commutes (r : R) (x : GradedMonoid (Piece A d)) :
    GradedMonoid.mk 0 (algebraMap A d r) * x =
      x * GradedMonoid.mk 0 (algebraMap A d r) := sorry

/-- Scalar multiplication agrees with multiplication by the degree-zero scalar image. -/
theorem algebraMap_smul (r : R) (x : GradedMonoid (Piece A d)) :
    r • x = GradedMonoid.mk 0 (algebraMap A d r) * x := sorry

/-- Even-variable coefficient pieces inherit their graded `R`-algebra structure. -/
noncomputable instance pieceGAlgebra : DirectSum.GAlgebra R (Piece A d) where
  toFun := algebraMap A d
  map_one := algebraMap_one A d
  map_mul := algebraMap_mul A d
  commutes := algebraMap_commutes A d
  smul_def := algebraMap_smul A d

/-- Even-degree adjoining multiplication obeys the Koszul commutativity rule. -/
theorem mul_comm (hd : Even d) (m n : ℕ) (x : Piece A d m) (y : Piece A d n) :
    GradedMonoid.GMul.mul x y =
      cast (congrArg (Piece A d) (Nat.add_comm n m))
        (((-1 : R) ^ (m * n)) • GradedMonoid.GMul.mul y x) := sorry

/-- Odd homogeneous elements square to zero after adjoining an even variable. -/
theorem sq_eq_zero_of_odd (hd : Even d) {m : ℕ} (hm : Odd m) (x : Piece A d m) :
    GradedMonoid.GMul.mul x x = 0 := sorry

/-- The strictly graded-commutative law selected by an evenness proof for the adjoined degree. -/
theorem pieceIsStrictlyCommutative (hd : Even d) :
    DirectSum.Graded.IsStrictlyCommutative R (Piece A d) := by
  exact {
    mul_comm := mul_comm A d hd
    sq_eq_zero_of_odd := sq_eq_zero_of_odd A d hd }

/-- Example 23.6.3 (Adjoining even variable) (Tag 09PI): the reusable bundled nonnegative
graded algebra obtained by adjoining a divided-power variable of even degree `d`.  The textbook's
positive-degree construction is its specialization under `0 < d`. -/
@[stacks 09PI "bundled even-variable algebra"]
def algebra (hd : Even d) : NonnegGradedAlgebra.{u, v} R where
  piece := Piece A d
  pieceAddCommGroup := fun _ ↦ inferInstance
  pieceModule := fun _ ↦ inferInstance
  pieceGSemiring := pieceGSemiring A d
  pieceGAlgebra := pieceGAlgebra A d
  pieceIsStrictlyCommutative := pieceIsStrictlyCommutative A d hd

/-- The constant-coefficient representative of a homogeneous base element. -/
def baseCoeff (m : ℕ) (x : A.piece m) : Piece A d m :=
  DFinsupp.single (zeroIndex d m)
    (cast (congrArg A.piece <|
      (Nat.sub_zero m).symm.trans <|
        congrArg (fun q ↦ m - q) (Nat.zero_mul d).symm) x)

/-- Constant-coefficient inclusion preserves addition. -/
theorem baseCoeff_add (m : ℕ) (x y : A.piece m) :
    baseCoeff A d m (x + y) = baseCoeff A d m x + baseCoeff A d m y := by
  unfold baseCoeff
  exact (congrArg (DFinsupp.single (zeroIndex d m))
    (Implementation.cast_add A ((Nat.sub_zero m).symm.trans (congrArg (fun q ↦ m - q) (Nat.zero_mul d).symm)) x y)).trans (DFinsupp.single_add _ _ _)

/-- Constant-coefficient inclusion preserves scalar multiplication. -/
theorem baseCoeff_smul (m : ℕ) (r : R) (x : A.piece m) :
    baseCoeff A d m (r • x) = r • baseCoeff A d m x := by
  unfold baseCoeff
  exact (congrArg (DFinsupp.single (zeroIndex d m))
    (Implementation.cast_smul A ((Nat.sub_zero m).symm.trans (congrArg (fun q ↦ m - q) (Nat.zero_mul d).symm)) r x)).trans (DFinsupp.single_smul r _)

/-- The degreewise linear constant-coefficient inclusion. -/
def baseMap (m : ℕ) : A.piece m →ₗ[R] Piece A d m where
  toFun := baseCoeff A d m
  map_add' := baseCoeff_add A d m
  map_smul' := baseCoeff_smul A d m

/-- Constant coefficients preserve the graded unit. -/
theorem baseMap_one : baseMap A d 0 GradedMonoid.GOne.one = GradedMonoid.GOne.one := by
  rfl

/-- Constant coefficients preserve homogeneous multiplication. -/
theorem baseMap_mul (m n : ℕ) (x : A.piece m) (y : A.piece n) :
    baseMap A d (m + n) (GradedMonoid.GMul.mul x y) =
      GradedMonoid.GMul.mul (baseMap A d m x) (baseMap A d n y) := sorry

/-- The canonical graded-algebra inclusion into an even-variable extension. -/
def inclusion (hd : Even d) : A ⟶ algebra A d hd where
  map := baseMap A d
  map_one := baseMap_one A d
  map_mul := baseMap_mul A d

/-- The homogeneous coefficient vector representing the `i`th divided monomial in the adjoined
even variable. -/
def dividedMonomial (i : ℕ) : Piece A d (i * d) :=
  DFinsupp.single ⟨i, le_refl (i * d)⟩
    (cast (congrArg A.piece (Nat.sub_self (i * d)).symm)
      (GradedMonoid.GOne.one : A.piece 0))

/-- The zeroth divided monomial is the graded unit. -/
@[simp]
theorem dividedMonomial_zero :
    dividedMonomial A d 0 =
      cast (congrArg (Piece A d) (Nat.zero_mul d).symm) GradedMonoid.GOne.one := by
  change dividedMonomial A d 0 =
    cast (congrArg (Piece A d) (Nat.zero_mul d).symm) (pieceOne A d)
  unfold dividedMonomial pieceOne
  rw [Implementation.cast_single A (fun i : ℕ ↦ i * d) (Nat.zero_mul d).symm]
  unfold zeroIndex
  apply congrArg (DFinsupp.single
    (β := fun i : {i : ℕ // i * d ≤ 0 * d} ↦ A.piece (0 * d - i * d))
    ⟨0, le_refl (0 * d)⟩)
  exact (Implementation.cast_comp _ _ _ _).symm

/-- Source divided monomials multiply with the canonical binomial coefficient. -/
theorem dividedMonomial_mul (i j : ℕ) :
    cast (congrArg (Piece A d) (Nat.add_mul i j d).symm)
        (GradedMonoid.GMul.mul (dividedMonomial A d i) (dividedMonomial A d j)) =
      Nat.choose (i + j) i • dividedMonomial A d (i + j) := sorry

/-- The homogeneous coefficient vector representing the adjoined even variable. -/
def generator : Piece A d d :=
  cast (congrArg (Piece A d) (Nat.one_mul d)) (dividedMonomial A d 1)

/-- The first divided monomial is the adjoined even generator. -/
@[simp]
theorem dividedMonomial_one :
    cast (congrArg (Piece A d) (Nat.one_mul d)) (dividedMonomial A d 1) =
      generator A d := by
  rfl

/-- The canonical inclusion is the constant-coefficient formula in every degree. -/
@[simp]
theorem inclusion_apply (hd : Even d) (m : ℕ) (x : A.piece m) :
    (inclusion A d hd).map m x = baseCoeff A d m x := by
  rfl

/-- Maps out of an even-variable extension are determined by their restriction to the base and
their values on all divided monomials. -/
theorem hom_ext (hd : Even d) {B : NonnegGradedAlgebra.{u, v} R}
    (f g : algebra A d hd ⟶ B) (hbase : inclusion A d hd ≫ f = inclusion A d hd ≫ g)
    (hmonomial : ∀ i, f.map (i * d) (dividedMonomial A d i) =
      g.map (i * d) (dividedMonomial A d i)) : f = g := sorry

/-- A divided-monomial family in degree `d`: its `i`th term has degree `i * d`, starts at the
unit, and multiplies with the binomial coefficient. -/
@[stacks 09PI "target divided monomials"]
structure DividedMonomials (B : NonnegGradedAlgebra.{u, v} R) (d : ℕ) where
  /-- The target value of the divided monomial `T ^ (i)`. -/
  coefficient (i : ℕ) : B.piece (i * d)
  /-- The zeroth divided monomial is the graded unit. -/
  coefficient_zero :
    coefficient 0 = cast (congrArg B.piece (Nat.zero_mul d).symm) GradedMonoid.GOne.one
  /-- Divided monomials multiply with the canonical binomial coefficient. -/
  coefficient_mul (i j : ℕ) :
    cast (congrArg B.piece (Nat.add_mul i j d).symm)
        (GradedMonoid.GMul.mul (coefficient i) (coefficient j)) =
      Nat.choose (i + j) i • coefficient (i + j)

namespace DividedMonomials

variable {B C : NonnegGradedAlgebra.{u, v} R} {d : ℕ}

/-- The defining unit and multiplication laws of a divided-monomial family. -/
theorem spec (t : DividedMonomials B d) :
    t.coefficient 0 =
        cast (congrArg B.piece (Nat.zero_mul d).symm) GradedMonoid.GOne.one ∧
      ∀ i j, cast (congrArg B.piece (Nat.add_mul i j d).symm)
          (GradedMonoid.GMul.mul (t.coefficient i) (t.coefficient j)) =
        Nat.choose (i + j) i • t.coefficient (i + j) := by
  exact ⟨t.coefficient_zero, t.coefficient_mul⟩

/-- Divided-monomial families are determined by their homogeneous coefficients. -/
@[ext]
theorem ext {s t : DividedMonomials B d}
    (h : ∀ i, s.coefficient i = t.coefficient i) : s = t := by
  cases s with
  | mk sc sz sm =>
    cases t with
    | mk tc tz tm =>
      have hc : sc = tc := funext h
      cases hc
      rfl

/-- The homogeneous coefficients obtained by applying a graded-algebra morphism to a
divided-monomial family. -/
def mapCoefficient (t : DividedMonomials B d) (f : NonnegGradedAlgebra.Hom B C) (i : ℕ) :
    C.piece (i * d) :=
  f.map (i * d) (t.coefficient i)

/-- Mapping a divided-monomial family preserves its zeroth coefficient. -/
theorem mapCoefficient_zero (t : DividedMonomials B d) (f : NonnegGradedAlgebra.Hom B C) :
    mapCoefficient t f 0 =
      cast (congrArg C.piece (Nat.zero_mul d).symm) GradedMonoid.GOne.one := by
  unfold mapCoefficient
  rw [t.coefficient_zero, Implementation.hom_map_cast f (Nat.zero_mul d).symm, f.map_one]

/-- Mapping a divided-monomial family preserves its binomial multiplication law. -/
theorem mapCoefficient_mul (t : DividedMonomials B d) (f : NonnegGradedAlgebra.Hom B C)
    (i j : ℕ) :
    cast (congrArg C.piece (Nat.add_mul i j d).symm)
        (GradedMonoid.GMul.mul (mapCoefficient t f i) (mapCoefficient t f j)) =
      Nat.choose (i + j) i • mapCoefficient t f (i + j) := by
  unfold mapCoefficient
  rw [← f.map_mul, ← Implementation.hom_map_cast f (Nat.add_mul i j d).symm,
    t.coefficient_mul, map_nsmul]

/-- A graded-algebra morphism transports a divided-monomial family coefficientwise. -/
def map (t : DividedMonomials B d) (f : NonnegGradedAlgebra.Hom B C) :
    DividedMonomials C d where
  coefficient := mapCoefficient t f
  coefficient_zero := mapCoefficient_zero t f
  coefficient_mul := mapCoefficient_mul t f

/-- Transporting divided monomials applies the morphism degreewise to their coefficients. -/
@[simp]
theorem map_coefficient (t : DividedMonomials B d) (f : NonnegGradedAlgebra.Hom B C) (i : ℕ) :
    (t.map f).coefficient i = f.map (i * d) (t.coefficient i) := by
  rfl

/-- Transport by the identity graded-algebra morphism fixes a divided-monomial family. -/
@[simp]
theorem map_id (t : DividedMonomials B d) :
    t.map (NonnegGradedAlgebra.Hom.id B) = t := by
  apply ext
  intro i
  rfl

/-- Transport of divided-monomial families respects composition. -/
@[simp]
theorem map_comp (t : DividedMonomials B d) (f : NonnegGradedAlgebra.Hom B C)
    {D : NonnegGradedAlgebra.{u, v} R} (g : NonnegGradedAlgebra.Hom C D) :
    t.map (NonnegGradedAlgebra.Hom.comp g f) = (t.map f).map g := by
  apply ext
  intro i
  rfl

/-- The divided monomials carried by the canonical even-variable algebra. -/
@[stacks 09PI "canonical source divided monomials"]
def source (A : NonnegGradedAlgebra.{u, v} R) (d : ℕ) (hd : Even d) :
    DividedMonomials (algebra A d hd) d where
  coefficient := dividedMonomial A d
  coefficient_zero := dividedMonomial_zero A d
  coefficient_mul := dividedMonomial_mul A d

/-- The coefficients of the canonical source family are the explicit divided monomials. -/
@[simp]
theorem source_coefficient (A : NonnegGradedAlgebra.{u, v} R) (d : ℕ) (hd : Even d)
    (i : ℕ) : (source A d hd).coefficient i = dividedMonomial A d i := by
  rfl

/-- A morphism out of the even-variable algebra records the images of all source divided
monomials as a target family. -/
def ofHom (A : NonnegGradedAlgebra.{u, v} R) (d : ℕ) (hd : Even d)
    (f : NonnegGradedAlgebra.Hom (algebra A d hd) B) : DividedMonomials B d :=
  (source A d hd).map f

/-- The family extracted from a morphism evaluates to that morphism on each source divided
monomial. -/
@[simp]
theorem ofHom_coefficient (A : NonnegGradedAlgebra.{u, v} R) (d : ℕ) (hd : Even d)
    (f : NonnegGradedAlgebra.Hom (algebra A d hd) B) (i : ℕ) :
    (ofHom A d hd f).coefficient i = f.map (i * d) (dividedMonomial A d i) := by
  rfl

/-- Extracting divided monomials from a composite morphism is coefficientwise transport of the
family extracted from the first morphism. -/
@[simp]
theorem ofHom_comp (A : NonnegGradedAlgebra.{u, v} R) (d : ℕ) (hd : Even d)
    (f : NonnegGradedAlgebra.Hom (algebra A d hd) B)
    (g : NonnegGradedAlgebra.Hom B C) :
    ofHom A d hd (NonnegGradedAlgebra.Hom.comp g f) = (ofHom A d hd f).map g := by
  apply ext
  intro i
  rfl

/-- The degree-`d` element represented by the first divided monomial. -/
def generator (t : DividedMonomials B d) : B.piece d :=
  cast (congrArg B.piece (Nat.one_mul d)) (t.coefficient 1)

/-- Transporting a divided-monomial family transports its degree-`d` generator. -/
@[simp]
theorem map_generator (t : DividedMonomials B d) (f : NonnegGradedAlgebra.Hom B C) :
    (t.map f).generator = f.map d t.generator := by
  change cast (congrArg C.piece (Nat.one_mul d))
    (f.map (1 * d) (t.coefficient 1)) =
    f.map d (cast (congrArg B.piece (Nat.one_mul d)) (t.coefficient 1))
  exact (Implementation.hom_map_cast f (Nat.one_mul d) (t.coefficient 1)).symm

/-- Divided powers on a target algebra provide the canonical divided-monomial coefficients of a
positive even homogeneous element. -/
def ofDividedPowers (gamma : NonnegGradedAlgebra.DividedPowers B) (q : ℕ)
    (x : B.piece (2 * (q + 1))) (i : ℕ) : B.piece (i * (2 * (q + 1))) :=
  cast (congrArg B.piece (Nat.mul_left_comm i 2 (q + 1)).symm) (gamma.gammaPiece i q x)

/-- The canonical divided-monomial coefficients start with the graded unit. -/
theorem ofDividedPowers_zero (gamma : NonnegGradedAlgebra.DividedPowers B) (q : ℕ)
    (x : B.piece (2 * (q + 1))) :
    ofDividedPowers gamma q x 0 =
      cast (congrArg B.piece (Nat.zero_mul (2 * (q + 1))).symm) GradedMonoid.GOne.one := by
  unfold ofDividedPowers NonnegGradedAlgebra.DividedPowers.gammaPiece
  rw [gamma.gamma_zero]
  unfold NonnegGradedAlgebra.oneEven NonnegGradedAlgebra.evenHom
  rw [DirectSum.component.of, dif_pos (Nat.zero_mul (q + 1)).symm]
  rw [Implementation.recOn_eq_cast (β := fun e : ℕ ↦ B.piece (2 * e))
    (Nat.zero_mul (q + 1)).symm]
  exact Implementation.cast_comp _ _ _ _

/-- Canonical divided-monomial coefficients multiply with the binomial coefficient. -/
theorem ofDividedPowers_mul (gamma : NonnegGradedAlgebra.DividedPowers B) (q i j : ℕ)
    (x : B.piece (2 * (q + 1))) :
    cast (congrArg B.piece (Nat.add_mul i j (2 * (q + 1))).symm)
        (GradedMonoid.GMul.mul
          (ofDividedPowers gamma q x i) (ofDividedPowers gamma q x j)) =
      Nat.choose (i + j) i • ofDividedPowers gamma q x (i + j) := sorry

/-- The divided-monomial family canonically induced by a target divided-power structure. -/
def ofGamma (gamma : NonnegGradedAlgebra.DividedPowers B) (q : ℕ)
    (x : B.piece (2 * (q + 1))) : DividedMonomials B (2 * (q + 1)) where
  coefficient := ofDividedPowers gamma q x
  coefficient_zero := ofDividedPowers_zero gamma q x
  coefficient_mul := fun i j ↦ ofDividedPowers_mul gamma q i j x

/-- The coefficients of the canonical family induced by divided powers are homogeneous divided
powers of the chosen element. -/
@[simp]
theorem ofGamma_coefficient (gamma : NonnegGradedAlgebra.DividedPowers B) (q i : ℕ)
    (x : B.piece (2 * (q + 1))) :
    (ofGamma gamma q x).coefficient i = ofDividedPowers gamma q x i := by
  rfl

/-- The generator of the canonical family induced by divided powers is the chosen homogeneous
element. -/
@[simp]
theorem ofGamma_generator (gamma : NonnegGradedAlgebra.DividedPowers B) (q : ℕ)
    (x : B.piece (2 * (q + 1))) : (ofGamma gamma q x).generator = x := by
  change cast (congrArg B.piece (Nat.one_mul (2 * (q + 1))))
    (ofDividedPowers gamma q x 1) = x
  unfold ofDividedPowers NonnegGradedAlgebra.DividedPowers.gammaPiece
  rw [gamma.gamma_one]
  have hpos : B.evenPositiveToEven (B.evenPositiveHom q x) = B.evenHom (q + 1) x := by
    exact DirectSum.toModule_lof R (M := fun e : ℕ ↦ B.piece (2 * (e + 1)))
      (φ := fun e ↦ B.evenHom (e + 1)) q x
  rw [hpos]
  change cast _ (cast _ ((DirectSum.component R ℕ (fun e ↦ B.piece (2 * e))
    (1 * (q + 1))) (B.evenHom (q + 1) x))) = x
  unfold NonnegGradedAlgebra.evenHom
  rw [DirectSum.component.of, dif_pos (Nat.one_mul (q + 1)).symm]
  rw [Implementation.recOn_eq_cast (β := fun e : ℕ ↦ B.piece (2 * e))
    (Nat.one_mul (q + 1)).symm]
  rw [cast_cast]
  exact Implementation.cast_roundtrip _ _ _

end DividedMonomials

/-- The degreewise evaluation map determined by a base map and divided monomials in the target. -/
def liftMap {B : NonnegGradedAlgebra.{u, v} R} (g : A ⟶ B)
    (t : DividedMonomials B d) (m : ℕ) : Piece A d m →ₗ[R] B.piece m :=
  Implementation.evalMap id A B d m g t.coefficient

/-- Even-variable evaluation preserves the graded unit. -/
theorem liftMap_one {B : NonnegGradedAlgebra.{u, v} R} (g : A ⟶ B)
    (t : DividedMonomials B d) :
    liftMap A d g t 0 GradedMonoid.GOne.one = GradedMonoid.GOne.one := sorry

/-- Even-variable evaluation preserves homogeneous multiplication when the adjoined degree is
even, so its target divided monomials commute with the base image without a Koszul sign. -/
theorem liftMap_mul (hd : Even d) {B : NonnegGradedAlgebra.{u, v} R} (g : A ⟶ B)
    (t : DividedMonomials B d) (m n : ℕ) (a : Piece A d m) (b : Piece A d n) :
    liftMap A d g t (m + n) (GradedMonoid.GMul.mul a b) =
      GradedMonoid.GMul.mul (liftMap A d g t m a) (liftMap A d g t n b) := sorry

/-- The explicit graded-algebra lift determined by a base map and target divided monomials. -/
def lift (hd : Even d) {B : NonnegGradedAlgebra.{u, v} R} (g : A ⟶ B)
    (t : DividedMonomials B d) : algebra A d hd ⟶ B where
  map := liftMap A d g t
  map_one := liftMap_one A d g t
  map_mul := liftMap_mul A d hd g t

/-- The explicit even-variable lift restricts to the prescribed base map. -/
@[simp]
theorem lift_base (hd : Even d) {B : NonnegGradedAlgebra.{u, v} R}
    (g : A ⟶ B) (t : DividedMonomials B d) : inclusion A d hd ≫ lift A d hd g t = g := sorry

/-- The explicit even-variable lift sends the generator to the first divided monomial. -/
@[simp]
theorem lift_generator (hd : Even d) {B : NonnegGradedAlgebra.{u, v} R}
    (g : A ⟶ B) (t : DividedMonomials B d) :
    (lift A d hd g t).map d (generator A d) = t.generator := sorry

/-- The explicit even-variable lift sends every divided monomial to its prescribed target
coefficient. -/
@[simp]
theorem lift_dividedMonomial (hd : Even d) {B : NonnegGradedAlgebra.{u, v} R}
    (g : A ⟶ B) (t : DividedMonomials B d) (i : ℕ) :
    (lift A d hd g t).map (i * d) (dividedMonomial A d i) = t.coefficient i := sorry

/-- Extracting the divided-monomial family of an even-variable lift recovers the prescribed
family. -/
@[simp]
theorem DividedMonomials.ofHom_lift (hd : Even d) {B : NonnegGradedAlgebra.{u, v} R}
    (g : A ⟶ B) (t : DividedMonomials B d) :
    DividedMonomials.ofHom A d hd (lift A d hd g t) = t := by
  apply DividedMonomials.ext
  intro i
  exact lift_dividedMonomial A d hd g t i

/-- Every morphism out of an even-variable extension is the lift of its base restriction and its
extracted divided-monomial family. -/
theorem hom_eq_lift (hd : Even d) {B : NonnegGradedAlgebra.{u, v} R}
    (f : algebra A d hd ⟶ B) :
    f = lift A d hd (inclusion A d hd ≫ f) (DividedMonomials.ofHom A d hd f) := by
  apply hom_ext A d hd
  · show inclusion A d hd ≫ f = inclusion A d hd ≫
      lift A d hd (inclusion A d hd ≫ f) (DividedMonomials.ofHom A d hd f)
    rw [lift_base]
  · show ∀ i, f.map (i * d) (dividedMonomial A d i) =
      (lift A d hd (inclusion A d hd ≫ f) (DividedMonomials.ofHom A d hd f)).map
        (i * d) (dividedMonomial A d i)
    intro i
    rw [lift_dividedMonomial]
    rfl

/-- Postcomposition of an even-variable lift acts on its base map and divided-monomial family. -/
@[simp]
theorem lift_comp (hd : Even d) {B C : NonnegGradedAlgebra.{u, v} R}
    (g : A ⟶ B) (t : DividedMonomials B d) (f : B ⟶ C) :
    lift A d hd g t ≫ f = lift A d hd (g ≫ f) (t.map f) := by
  apply hom_ext A d hd
  · show inclusion A d hd ≫ (lift A d hd g t ≫ f) =
      inclusion A d hd ≫ lift A d hd (g ≫ f) (t.map f)
    rw [← Category.assoc, lift_base, lift_base]
  · show ∀ i, (lift A d hd g t ≫ f).map (i * d) (dividedMonomial A d i) =
      (lift A d hd (g ≫ f) (t.map f)).map (i * d) (dividedMonomial A d i)
    intro i
    change f.map (i * d) ((lift A d hd g t).map (i * d) (dividedMonomial A d i)) = _
    rw [lift_dividedMonomial, lift_dividedMonomial]
    rfl

/-- A morphism from the even-variable extension has the prescribed base restriction and divided
monomial values. -/
def IsLift (hd : Even d) {B : NonnegGradedAlgebra.{u, v} R}
    (g : A ⟶ B) (t : DividedMonomials B d) (f : algebra A d hd ⟶ B) : Prop :=
  inclusion A d hd ≫ f = g ∧
    ∀ i, f.map (i * d) (dividedMonomial A d i) = t.coefficient i

/-- The explicit even-variable lift satisfies its universal specification. -/
theorem lift_isLift (hd : Even d) {B : NonnegGradedAlgebra.{u, v} R}
    (g : A ⟶ B) (t : DividedMonomials B d) : IsLift A d hd g t (lift A d hd g t) := by
  exact ⟨lift_base A d hd g t, lift_dividedMonomial A d hd g t⟩

/-- Every morphism satisfying the even-variable universal specification is the explicit lift. -/
theorem lift_unique (hd : Even d) {B : NonnegGradedAlgebra.{u, v} R}
    (g : A ⟶ B) (t : DividedMonomials B d) (f : algebra A d hd ⟶ B)
    (hf : IsLift A d hd g t f) : f = lift A d hd g t := by
  apply hom_ext A d hd
  · show inclusion A d hd ≫ f = inclusion A d hd ≫ lift A d hd g t
    rw [lift_base]
    exact hf.1
  · show ∀ i, f.map (i * d) (dividedMonomial A d i) =
      (lift A d hd g t).map (i * d) (dividedMonomial A d i)
    intro i
    rw [lift_dividedMonomial]
    exact hf.2 i

/-- A base map and a divided-monomial target family determine a unique even-variable lift. -/
theorem existsUnique_lift (hd : Even d) {B : NonnegGradedAlgebra.{u, v} R}
    (g : A ⟶ B) (t : DividedMonomials B d) :
    ∃! f : algebra A d hd ⟶ B, IsLift A d hd g t f := by
  exact ⟨lift A d hd g t, lift_isLift A d hd g t, fun f hf ↦
    lift_unique A d hd g t f hf⟩

end Even

end NonnegGradedAlgebra.Adjoin
