/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainDGAlgebra.Hom

/-!
# Opposite Cochain Differential Graded Algebras

This file owns the Koszul-twisted opposite of a cochain differential graded algebra.  The
underlying cochain complex, differential, and unit are unchanged; multiplication is reversed with
the sign `(-1)^(i * j)` on elements of degrees `i` and `j`.

The construction is also functorial on cochain-DGA homomorphisms.
-/

@[expose] public section

universe u v w x

open CategoryTheory

namespace CochainDGAlgebra

variable {R : Type u} [CommRing R]

/-- The Koszul sign used to reverse homogeneous multiplication. -/
@[stacks 09JG "Koszul sign for opposite DGAs"]
def oppositeSign (R : Type u) [CommRing R] (i j : ℤ) : R :=
  ((i * j).negOnePow : R)

/-- The opposite Koszul sign is trivial when the left degree is zero. -/
@[simp]
theorem oppositeSign_zero_left (j : ℤ) :
    oppositeSign R 0 j = (1 : R) := by
  simp [oppositeSign]

/-- The opposite Koszul sign is trivial when the right degree is zero. -/
@[simp]
theorem oppositeSign_zero_right (i : ℤ) :
    oppositeSign R i 0 = (1 : R) := by
  simp [oppositeSign]

/-- The opposite Koszul sign is symmetric in the two degrees. -/
@[simp]
theorem oppositeSign_comm (i j : ℤ) :
    oppositeSign R i j = oppositeSign R j i := by
  unfold oppositeSign
  rw [mul_comm i j]

/-- The square of the opposite Koszul sign is one. -/
@[simp]
theorem oppositeSign_mul_self (i j : ℤ) :
    oppositeSign R i j * oppositeSign R i j = (1 : R) := by
  simp only [oppositeSign, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self,
    Units.val_one, Int.cast_one]

/-- Applying the same opposite Koszul sign twice is the identity scalar action. -/
@[simp]
theorem oppositeSign_smul_oppositeSign {M : Type v} [AddCommMonoid M] [Module R M]
    (i j : ℤ) (x : M) :
    oppositeSign R i j • (oppositeSign R i j • x) = x := by
  rw [smul_smul, oppositeSign_mul_self, one_smul]

/-- The opposite Koszul sign is multiplicative in the right degree. -/
theorem oppositeSign_add_right (p q r : ℤ) :
    oppositeSign R p (q + r) = oppositeSign R p q * oppositeSign R p r := by
  simp only [oppositeSign, mul_add, Int.negOnePow_add, Units.val_mul, Int.cast_mul]

/-- The opposite Koszul sign is multiplicative in the left degree. -/
theorem oppositeSign_add_left (p q r : ℤ) :
    oppositeSign R (p + q) r = oppositeSign R p r * oppositeSign R q r := by
  simp only [oppositeSign, add_mul, Int.negOnePow_add, Units.val_mul, Int.cast_mul]

/-- Incrementing the left degree contributes the sign of the right degree. -/
theorem oppositeSign_add_one_left (i j : ℤ) :
    oppositeSign R (i + 1) j = oppositeSign R i j * (j.negOnePow : R) := by
  simpa only [oppositeSign, _root_.one_mul] using oppositeSign_add_left (R := R) i 1 j

/-- Incrementing the right degree contributes the sign of the left degree. -/
theorem oppositeSign_add_one_right (i j : ℤ) :
    oppositeSign R i (j + 1) = oppositeSign R i j * (i.negOnePow : R) := by
  simpa only [oppositeSign, _root_.mul_one] using oppositeSign_add_right (R := R) i j 1

/-- The signs in the two associations of a triple opposite product agree. -/
theorem oppositeSign_assoc (i j k : ℤ) :
    oppositeSign R (i + j) k * oppositeSign R i j =
      oppositeSign R i (j + k) * oppositeSign R j k := by
  rw [oppositeSign_add_left, oppositeSign_add_right]
  ac_rfl

/- Transport through degree equalities preserves the module operations. -/
private theorem cast_add (X : ℤ → ModuleCat.{v} R) {i j : ℤ} (h : i = j)
    (a b : X i) :
    cast (congrArg (fun n : ℤ ↦ (X n : Type v)) h) (a + b) =
      cast (congrArg (fun n : ℤ ↦ (X n : Type v)) h) a +
        cast (congrArg (fun n : ℤ ↦ (X n : Type v)) h) b := by
  cases h
  rfl

private theorem cast_smul (X : ℤ → ModuleCat.{v} R) {i j : ℤ} (h : i = j)
    (r : R) (a : X i) :
    cast (congrArg (fun n : ℤ ↦ (X n : Type v)) h) (r • a) =
      r • cast (congrArg (fun n : ℤ ↦ (X n : Type v)) h) a := by
  cases h
  rfl

private theorem cast_map (X : ℤ → ModuleCat.{v} R) (Y : ℤ → ModuleCat.{w} R)
    (f : ∀ n, X n →ₗ[R] Y n) {i j : ℤ} (h : i = j) (a : X i) :
    f j (cast (congrArg (fun n : ℤ ↦ (X n : Type v)) h) a) =
      cast (congrArg (fun n : ℤ ↦ (Y n : Type w)) h) (f i a) := by
  cases h
  rfl

private theorem cast_mul_left (A : CochainDGAlgebra.{u, v} R) {i i' : ℤ}
    (h : i = i') (j : ℤ) (a : A.X i) (b : A.X j) :
    A.mul i' j (cast (congrArg (fun n : ℤ ↦ (A.X n : Type v)) h) a) b =
      cast (congrArg (fun n : ℤ ↦ (A.X n : Type v)) (congrArg (· + j) h))
        (A.mul i j a b) := by
  cases h
  rfl

private theorem cast_mul_right (A : CochainDGAlgebra.{u, v} R) (i : ℤ) {j j' : ℤ}
    (h : j = j') (a : A.X i) (b : A.X j) :
    A.mul i j' a (cast (congrArg (fun n : ℤ ↦ (A.X n : Type v)) h) b) =
      cast (congrArg (fun n : ℤ ↦ (A.X n : Type v)) (congrArg (i + ·) h))
        (A.mul i j a b) := by
  cases h
  rfl

/-- The value of the Koszul-twisted reverse product on two homogeneous elements. -/
@[stacks 09JG "homogeneous opposite multiplication"]
def oppositeMulValue (A : CochainDGAlgebra.{u, v} R) (i j : ℤ) (a : A.X i) (b : A.X j) :
    A.X (i + j) :=
  cast (congrArg (fun n : ℤ ↦ (A.X n : Type v)) (add_comm j i))
    (oppositeSign R i j • A.mul j i b a)

/-- The opposite product value is additive in its right input. -/
theorem oppositeMulValue_add_right (A : CochainDGAlgebra.{u, v} R) (i j : ℤ)
    (a : A.X i) (b₁ b₂ : A.X j) :
    oppositeMulValue A i j a (b₁ + b₂) =
      oppositeMulValue A i j a b₁ + oppositeMulValue A i j a b₂ := by
  simp only [oppositeMulValue, map_add, LinearMap.add_apply, smul_add, cast_add A.X (add_comm j i)]

/-- The opposite product value is linear in its right input. -/
theorem oppositeMulValue_smul_right (A : CochainDGAlgebra.{u, v} R) (i j : ℤ)
    (a : A.X i) (r : R) (b : A.X j) :
    oppositeMulValue A i j a (r • b) = r • oppositeMulValue A i j a b := by
  simp only [oppositeMulValue, map_smul, LinearMap.smul_apply]
  rw [smul_comm, cast_smul A.X (add_comm j i)]

/-- The reverse product by a fixed left input as a linear map. -/
@[stacks 09JG "linear opposite multiplication"]
def oppositeMulRight (A : CochainDGAlgebra.{u, v} R) (i j : ℤ) (a : A.X i) :
    A.X j →ₗ[R] A.X (i + j) where
  toFun := oppositeMulValue A i j a
  map_add' := oppositeMulValue_add_right A i j a
  map_smul' := oppositeMulValue_smul_right A i j a

/-- The linear reverse product is additive in its fixed left input. -/
theorem oppositeMulRight_add (A : CochainDGAlgebra.{u, v} R) (i j : ℤ)
    (a₁ a₂ : A.X i) :
    oppositeMulRight A i j (a₁ + a₂) =
      oppositeMulRight A i j a₁ + oppositeMulRight A i j a₂ := by
  apply LinearMap.ext
  intro b
  change oppositeMulValue A i j (a₁ + a₂) b =
    oppositeMulValue A i j a₁ b + oppositeMulValue A i j a₂ b
  simp only [oppositeMulValue, map_add, smul_add, cast_add A.X (add_comm j i)]

/-- The linear reverse product is linear in its fixed left input. -/
theorem oppositeMulRight_smul (A : CochainDGAlgebra.{u, v} R) (i j : ℤ)
    (r : R) (a : A.X i) :
    oppositeMulRight A i j (r • a) = r • oppositeMulRight A i j a := by
  apply LinearMap.ext
  intro b
  change oppositeMulValue A i j (r • a) b = r • oppositeMulValue A i j a b
  simp only [oppositeMulValue, map_smul]
  rw [smul_comm, cast_smul A.X (add_comm j i)]

/-- Koszul-twisted reverse multiplication as a curried bilinear map. -/
@[stacks 09JG "bilinear opposite multiplication"]
def oppositeMul (A : CochainDGAlgebra.{u, v} R) (i j : ℤ) :
    A.X i →ₗ[R] A.X j →ₗ[R] A.X (i + j) where
  toFun := oppositeMulRight A i j
  map_add' := oppositeMulRight_add A i j
  map_smul' := oppositeMulRight_smul A i j

/-- Opposite multiplication is the transported signed reverse product. -/
@[simp, stacks 09JG "opposite multiplication computation"]
theorem oppositeMul_apply (A : CochainDGAlgebra.{u, v} R)
    (i j : ℤ) (a : A.X i) (b : A.X j) :
    oppositeMul A i j a b =
      cast (congrArg (fun n : ℤ ↦ (A.X n : Type v)) (add_comm j i))
        (oppositeSign R i j • A.mul j i b a) := rfl

/-- Koszul-twisted reverse multiplication is associative. -/
theorem oppositeMul_assoc_apply (A : CochainDGAlgebra.{u, v} R) (i j k : ℤ)
    (a : A.X i) (b : A.X j) (c : A.X k) :
    cast (congrArg (fun n : ℤ ↦ (A.X n : Type v)) (add_assoc i j k))
        (oppositeMul A (i + j) k (oppositeMul A i j a b) c) =
      oppositeMul A i (j + k) a (oppositeMul A j k b c) := by
  simp only [oppositeMul_apply, cast_smul A.X (add_comm j i),
    cast_smul A.X (add_comm k j), cast_smul A.X (add_comm k (i + j)),
    cast_smul A.X (add_comm (j + k) i), cast_smul A.X (add_assoc i j k),
    cast_mul_left A (add_comm k j) i, cast_mul_right A k (add_comm j i),
    map_smul, LinearMap.smul_apply, smul_smul, cast_cast]
  rw [← A.mul_assoc k j i c b a]
  simp only [cast_cast]
  rw [_root_.mul_comm (oppositeSign R i j), oppositeSign_assoc,
    _root_.mul_comm (oppositeSign R i (j + k))]

/-- The original unit acts on the left for opposite multiplication. -/
theorem oppositeMul_one_mul_apply (A : CochainDGAlgebra.{u, v} R) (n : ℤ) (a : A.X n) :
    cast (congrArg (fun i : ℤ ↦ (A.X i : Type v)) (zero_add n))
      (oppositeMul A 0 n A.one a) = a := by
  simpa only [oppositeMul_apply, oppositeSign_zero_left, one_smul, cast_cast] using
    A.mul_one n a

/-- The original unit acts on the right for opposite multiplication. -/
theorem oppositeMul_mul_one_apply (A : CochainDGAlgebra.{u, v} R) (n : ℤ) (a : A.X n) :
    cast (congrArg (fun i : ℤ ↦ (A.X i : Type v)) (add_zero n))
      (oppositeMul A n 0 a A.one) = a := by
  simpa only [oppositeMul_apply, oppositeSign_zero_right, one_smul, cast_cast] using
    A.one_mul n a

/-- Opposite multiplication satisfies the cochain Leibniz rule. -/
theorem oppositeMul_leibniz_apply (A : CochainDGAlgebra.{u, v} R) (n m : ℤ)
    (a : A.X n) (b : A.X m) :
    A.d (n + m) (oppositeMul A n m a b) =
      cast (congrArg (fun i : ℤ ↦ (A.X i : Type v))
          (CochainDGAlgebra.leftLeibnizIndex n m))
          (oppositeMul A (n + 1) m (A.d n a) b) +
        n.negOnePow •
          cast (congrArg (fun i : ℤ ↦ (A.X i : Type v))
            (CochainDGAlgebra.rightLeibnizIndex n m))
            (oppositeMul A n (m + 1) a (A.d m b)) := by
  have hn : (n.negOnePow : R) * (n.negOnePow : R) = 1 := by
    simpa only [oppositeSign, _root_.mul_one] using oppositeSign_mul_self (R := R) n 1
  have hs : (n.negOnePow : R) * oppositeSign R n (m + 1) = oppositeSign R n m := by
    rw [oppositeSign_add_one_right, mul_left_comm, hn, _root_.mul_one]
  have h := A.leibniz m n b a
  simp only [Units.smul_def, ← Int.cast_smul_eq_zsmul R] at h ⊢
  change (A.d (n + m)).hom (oppositeMul A n m a b) = _
  simp only [oppositeMul_apply,
    cast_map A.X (fun i ↦ A.X (i + 1)) (fun i ↦ (A.d i).hom) (add_comm m n),
    map_smul]
  rw [h]
  simp only [cast_add (fun i ↦ A.X (i + 1)) (add_comm m n),
    cast_smul (fun i ↦ A.X (i + 1)) (add_comm m n),
    cast_smul A.X (leftLeibnizIndex n m), cast_smul A.X (rightLeibnizIndex n m),
    cast_smul A.X (add_comm m (n + 1)), cast_smul A.X (add_comm (m + 1) n),
    cast_cast, smul_add, smul_smul, oppositeSign_add_one_left, hs]
  exact _root_.add_comm _ _

/-- Definition 22.11.1 (09JG): the opposite cochain differential graded algebra has the same
underlying complex and unit, with Koszul-twisted reverse multiplication. -/
@[reducible, stacks 09JG]
def opposite (A : CochainDGAlgebra.{u, v} R) : CochainDGAlgebra.{u, v} R where
  toCochainComplex := A.toCochainComplex
  mul := oppositeMul A
  one := A.one
  mul_assoc := oppositeMul_assoc_apply A
  one_mul := oppositeMul_one_mul_apply A
  mul_one := oppositeMul_mul_one_apply A
  leibniz := oppositeMul_leibniz_apply A

/-- The opposite DGA has the same underlying cochain complex. -/
@[simp]
theorem opposite_toCochainComplex (A : CochainDGAlgebra.{u, v} R) :
    A.opposite.toCochainComplex = A.toCochainComplex := rfl

/-- The degree-`n` component of the opposite DGA is the original component. -/
@[simp]
theorem opposite_X (A : CochainDGAlgebra.{u, v} R) (n : ℤ) :
    A.opposite.X n = A.X n := rfl

/-- The differential of the opposite DGA is the original differential. -/
@[simp]
theorem opposite_d (A : CochainDGAlgebra.{u, v} R) (n : ℤ) :
    A.opposite.d n = A.d n := rfl

/-- The unit of the opposite DGA is the original unit. -/
@[simp]
theorem opposite_one (A : CochainDGAlgebra.{u, v} R) :
    A.opposite.one = A.one := rfl

/-- Multiplication in the opposite DGA is the transported Koszul-twisted reverse product. -/
@[simp, stacks 09JG "opposite DGA multiplication computation"]
theorem opposite_mul_apply (A : CochainDGAlgebra.{u, v} R)
    (i j : ℤ) (a : A.X i) (b : A.X j) :
    A.opposite.mul i j a b =
      cast (congrArg (fun n : ℤ ↦ (A.X n : Type v)) (add_comm j i))
        (oppositeSign R i j • A.mul j i b a) := rfl

/-- Applying opposite multiplication twice recovers the original homogeneous product. -/
private theorem opposite_opposite_mul_apply (A : CochainDGAlgebra.{u, v} R) (i j : ℤ)
    (a : A.X i) (b : A.X j) :
    A.opposite.opposite.mul i j a b = A.mul i j a b := by
  change oppositeMul A.opposite i j a b = A.mul i j a b
  rw [oppositeMul_apply, opposite_mul_apply]
  simp only [cast_smul A.X (add_comm j i), cast_cast, cast_eq,
    oppositeSign_comm j i, oppositeSign_smul_oppositeSign]

/-- Taking the opposite DGA twice recovers the original DGA. -/
@[simp, stacks 09JG "double opposite DGAs"]
theorem opposite_opposite (A : CochainDGAlgebra.{u, v} R) :
    A.opposite.opposite = A := by
  have hmul : A.opposite.opposite.mul = A.mul := by
    funext i j
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro b
    exact opposite_opposite_mul_apply A i j a b
  cases A
  dsimp only [opposite] at hmul ⊢
  congr 1

namespace Hom

variable {A : CochainDGAlgebra.{u, v} R} {B : CochainDGAlgebra.{u, w} R}
  {C : CochainDGAlgebra.{u, x} R}

/-- Preservation of opposite multiplication by a cochain-DGA homomorphism. -/
theorem opposite_map_mul (f : Hom A B) (n m : ℤ) (a : A.X n) (b : A.X m) :
    f (n + m) (oppositeMul A n m a b) =
      oppositeMul B n m (f n a) (f m b) := by
  change f.map (n + m) (oppositeMul A n m a b) =
    oppositeMul B n m (f.map n a) (f.map m b)
  simp only [oppositeMul_apply, cast_map A.X B.X f.map (add_comm m n), map_smul, f.map_mul]

/-- A cochain-DGA homomorphism induces a homomorphism between opposite DGAs. -/
@[stacks 09JG "opposite of a DG-algebra homomorphism"]
def opposite (f : Hom A B) : Hom A.opposite B.opposite where
  map := f.map
  comm_d := f.comm_d
  map_one := f.map_one
  map_mul := opposite_map_mul f

/-- The underlying cochain map of the opposite homomorphism is unchanged. -/
@[simp, stacks 09JG "underlying map of an opposite homomorphism"]
theorem opposite_toCochainMap {A B : CochainDGAlgebra.{u, v} R} (f : Hom A B) :
    f.opposite.toCochainMap = f.toCochainMap := rfl

/-- The opposite homomorphism acts degreewise as the original homomorphism. -/
@[simp, stacks 09JG "opposite homomorphism evaluation"]
theorem opposite_apply (f : Hom A B) (n : ℤ) (a : A.X n) :
    f.opposite n a = f n a := rfl

/-- Taking the opposite of an identity homomorphism gives an identity homomorphism. -/
@[simp, stacks 09JG "opposite homomorphism identity"]
theorem opposite_id (A : CochainDGAlgebra.{u, v} R) :
    (Hom.id A).opposite = Hom.id A.opposite := rfl

/-- Taking opposites preserves composition of cochain-DGA homomorphisms. -/
@[simp, stacks 09JG "opposite homomorphism composition"]
theorem opposite_comp (g : Hom B C) (f : Hom A B) :
    (Hom.comp g f).opposite = Hom.comp g.opposite f.opposite := rfl

end Hom

/-- The endofunctor taking a cochain DGA and its homomorphisms to their opposites. -/
@[stacks 09JG "opposite cochain-DGA functor"]
def oppositeFunctor (R : Type u) [CommRing R] :
    CochainDGAlgebra.{u, v} R ⥤ CochainDGAlgebra.{u, v} R where
  obj := opposite
  map := Hom.opposite
  map_id := Hom.opposite_id
  map_comp := fun f g ↦ Hom.opposite_comp g f

/-- The opposite functor acts on objects by `CochainDGAlgebra.opposite`. -/
@[simp, stacks 09JG "opposite functor on objects"]
theorem oppositeFunctor_obj (A : CochainDGAlgebra.{u, v} R) :
    (oppositeFunctor R).obj A = A.opposite := rfl

/-- The opposite functor acts on morphisms by `CochainDGAlgebra.Hom.opposite`. -/
@[simp, stacks 09JG "opposite functor on morphisms"]
theorem oppositeFunctor_map {A B : CochainDGAlgebra.{u, v} R} (f : A ⟶ B) :
    (oppositeFunctor R).map f = f.opposite := rfl

end CochainDGAlgebra
