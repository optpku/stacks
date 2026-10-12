/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
    oppositeSign R 0 j = (1 : R) := sorry

/-- The opposite Koszul sign is trivial when the right degree is zero. -/
@[simp]
theorem oppositeSign_zero_right (i : ℤ) :
    oppositeSign R i 0 = (1 : R) := sorry

/-- The opposite Koszul sign is symmetric in the two degrees. -/
@[simp]
theorem oppositeSign_comm (i j : ℤ) :
    oppositeSign R i j = oppositeSign R j i := sorry

/-- The square of the opposite Koszul sign is one. -/
@[simp]
theorem oppositeSign_mul_self (i j : ℤ) :
    oppositeSign R i j * oppositeSign R i j = (1 : R) := sorry

/-- Applying the same opposite Koszul sign twice is the identity scalar action. -/
@[simp]
theorem oppositeSign_smul_oppositeSign {M : Type v} [AddCommMonoid M] [Module R M]
    (i j : ℤ) (x : M) :
    oppositeSign R i j • (oppositeSign R i j • x) = x := sorry

/-- The opposite Koszul sign is multiplicative in the right degree. -/
theorem oppositeSign_add_right (p q r : ℤ) :
    oppositeSign R p (q + r) = oppositeSign R p q * oppositeSign R p r := sorry

/-- The opposite Koszul sign is multiplicative in the left degree. -/
theorem oppositeSign_add_left (p q r : ℤ) :
    oppositeSign R (p + q) r = oppositeSign R p r * oppositeSign R q r := sorry

/-- Incrementing the left degree contributes the sign of the right degree. -/
theorem oppositeSign_add_one_left (i j : ℤ) :
    oppositeSign R (i + 1) j = oppositeSign R i j * (j.negOnePow : R) := sorry

/-- Incrementing the right degree contributes the sign of the left degree. -/
theorem oppositeSign_add_one_right (i j : ℤ) :
    oppositeSign R i (j + 1) = oppositeSign R i j * (i.negOnePow : R) := sorry

/-- The signs in the two associations of a triple opposite product agree. -/
theorem oppositeSign_assoc (i j k : ℤ) :
    oppositeSign R (i + j) k * oppositeSign R i j =
      oppositeSign R i (j + k) * oppositeSign R j k := sorry

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
      oppositeMulValue A i j a b₁ + oppositeMulValue A i j a b₂ := sorry

/-- The opposite product value is linear in its right input. -/
theorem oppositeMulValue_smul_right (A : CochainDGAlgebra.{u, v} R) (i j : ℤ)
    (a : A.X i) (r : R) (b : A.X j) :
    oppositeMulValue A i j a (r • b) = r • oppositeMulValue A i j a b := sorry

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
      oppositeMulRight A i j a₁ + oppositeMulRight A i j a₂ := sorry

/-- The linear reverse product is linear in its fixed left input. -/
theorem oppositeMulRight_smul (A : CochainDGAlgebra.{u, v} R) (i j : ℤ)
    (r : R) (a : A.X i) :
    oppositeMulRight A i j (r • a) = r • oppositeMulRight A i j a := sorry

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
        (oppositeSign R i j • A.mul j i b a) := sorry

/-- Koszul-twisted reverse multiplication is associative. -/
theorem oppositeMul_assoc_apply (A : CochainDGAlgebra.{u, v} R) (i j k : ℤ)
    (a : A.X i) (b : A.X j) (c : A.X k) :
    cast (congrArg (fun n : ℤ ↦ (A.X n : Type v)) (add_assoc i j k))
        (oppositeMul A (i + j) k (oppositeMul A i j a b) c) =
      oppositeMul A i (j + k) a (oppositeMul A j k b c) := sorry

/-- The original unit acts on the left for opposite multiplication. -/
theorem oppositeMul_one_mul_apply (A : CochainDGAlgebra.{u, v} R) (n : ℤ) (a : A.X n) :
    cast (congrArg (fun i : ℤ ↦ (A.X i : Type v)) (zero_add n))
      (oppositeMul A 0 n A.one a) = a := sorry

/-- The original unit acts on the right for opposite multiplication. -/
theorem oppositeMul_mul_one_apply (A : CochainDGAlgebra.{u, v} R) (n : ℤ) (a : A.X n) :
    cast (congrArg (fun i : ℤ ↦ (A.X i : Type v)) (add_zero n))
      (oppositeMul A n 0 a A.one) = a := sorry

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
            (oppositeMul A n (m + 1) a (A.d m b)) := sorry

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
    A.opposite.toCochainComplex = A.toCochainComplex := sorry

/-- The degree-`n` component of the opposite DGA is the original component. -/
@[simp]
theorem opposite_X (A : CochainDGAlgebra.{u, v} R) (n : ℤ) :
    A.opposite.X n = A.X n := sorry

/-- The differential of the opposite DGA is the original differential. -/
@[simp]
theorem opposite_d (A : CochainDGAlgebra.{u, v} R) (n : ℤ) :
    A.opposite.d n = A.d n := sorry

/-- The unit of the opposite DGA is the original unit. -/
@[simp]
theorem opposite_one (A : CochainDGAlgebra.{u, v} R) :
    A.opposite.one = A.one := sorry

/-- Multiplication in the opposite DGA is the transported Koszul-twisted reverse product. -/
@[simp, stacks 09JG "opposite DGA multiplication computation"]
theorem opposite_mul_apply (A : CochainDGAlgebra.{u, v} R)
    (i j : ℤ) (a : A.X i) (b : A.X j) :
    A.opposite.mul i j a b =
      cast (congrArg (fun n : ℤ ↦ (A.X n : Type v)) (add_comm j i))
        (oppositeSign R i j • A.mul j i b a) := sorry

/-- Applying opposite multiplication twice recovers the original homogeneous product. -/
private theorem opposite_opposite_mul_apply (A : CochainDGAlgebra.{u, v} R) (i j : ℤ)
    (a : A.X i) (b : A.X j) :
    A.opposite.opposite.mul i j a b = A.mul i j a b := sorry

/-- Taking the opposite DGA twice recovers the original DGA. -/
@[simp, stacks 09JG "double opposite DGAs"]
theorem opposite_opposite (A : CochainDGAlgebra.{u, v} R) :
    A.opposite.opposite = A := sorry

namespace Hom

variable {A : CochainDGAlgebra.{u, v} R} {B : CochainDGAlgebra.{u, w} R}
  {C : CochainDGAlgebra.{u, x} R}

/-- Preservation of opposite multiplication by a cochain-DGA homomorphism. -/
theorem opposite_map_mul (f : Hom A B) (n m : ℤ) (a : A.X n) (b : A.X m) :
    f (n + m) (oppositeMul A n m a b) =
      oppositeMul B n m (f n a) (f m b) := sorry

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
    f.opposite.toCochainMap = f.toCochainMap := sorry

/-- The opposite homomorphism acts degreewise as the original homomorphism. -/
@[simp, stacks 09JG "opposite homomorphism evaluation"]
theorem opposite_apply (f : Hom A B) (n : ℤ) (a : A.X n) :
    f.opposite n a = f n a := sorry

/-- Taking the opposite of an identity homomorphism gives an identity homomorphism. -/
@[simp, stacks 09JG "opposite homomorphism identity"]
theorem opposite_id (A : CochainDGAlgebra.{u, v} R) :
    (Hom.id A).opposite = Hom.id A.opposite := sorry

/-- Taking opposites preserves composition of cochain-DGA homomorphisms. -/
@[simp, stacks 09JG "opposite homomorphism composition"]
theorem opposite_comp (g : Hom B C) (f : Hom A B) :
    (Hom.comp g f).opposite = Hom.comp g.opposite f.opposite := sorry

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
    (oppositeFunctor R).obj A = A.opposite := sorry

/-- The opposite functor acts on morphisms by `CochainDGAlgebra.Hom.opposite`. -/
@[simp, stacks 09JG "opposite functor on morphisms"]
theorem oppositeFunctor_map {A B : CochainDGAlgebra.{u, v} R} (f : A ⟶ B) :
    (oppositeFunctor R).map f = f.opposite := sorry

end CochainDGAlgebra
