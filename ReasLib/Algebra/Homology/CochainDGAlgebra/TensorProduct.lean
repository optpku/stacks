module

public import ReasLib.Algebra.Homology.CochainDGAlgebra.Hom
public import ReasLib.Algebra.Category.ModuleCat.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.CategoryTheory.Limits.Shapes.Countable

/-!
# Tensor Products of Cochain Differential Graded Algebras

This file owns the Koszul tensor product of cochain differential graded algebras.  Its underlying
complex is the canonical total tensor complex.  On homogeneous pure tensors its multiplication is

`(a ⊗ b) * (a' ⊗ b') = (-1)^(deg b * deg a') (a * a') ⊗ (b * b')`.

The construction is functorial in both algebra variables.
-/

@[expose] public section

noncomputable section

universe u v w v₁ v₂

open CategoryTheory
open ComplexShape HomologicalComplex
open scoped TensorProduct

namespace CochainDGAlgebra

variable {R : Type u} [CommRing R]

namespace Tensor

/-- The canonical total degree of a homogeneous tensor summand. -/
@[stacks 065W "total-degree bookkeeping for the DGA tensor product"]
theorem totalDegree (p q : ℤ) :
    (up ℤ).π (up ℤ) (up ℤ) (p, q) = p + q := sorry

/-- The degree-zero tensor summand has total degree zero. -/
@[stacks 065W "degree-zero tensor summand"]
theorem zeroTotalDegree :
    (up ℤ).π (up ℤ) (up ℤ) (0, 0) = 0 := sorry

/-- Multiplying summands of bidegrees `(p, q)` and `(p', q')` has the expected total degree. -/
@[stacks 065W "multiplicative total-degree bookkeeping"]
theorem mulTotalDegree (p q p' q' : ℤ) :
    (up ℤ).π (up ℤ) (up ℤ) (p + p', q + q') = (p + q) + (p' + q') := sorry

/-- The first differential summand has total degree `p + q + 1`. -/
@[stacks 065W "left differential total-degree bookkeeping"]
theorem dLeftTotalDegree (p q : ℤ) :
    (up ℤ).π (up ℤ) (up ℤ) (p + 1, q) = p + q + 1 := sorry

/-- The second differential summand has total degree `p + q + 1`. -/
@[stacks 065W "right differential total-degree bookkeeping"]
theorem dRightTotalDegree (p q : ℤ) :
    (up ℤ).π (up ℤ) (up ℤ) (p, q + 1) = p + q + 1 := sorry

variable (A : CochainDGAlgebra.{u, v} R) (B : CochainDGAlgebra.{u, w} R)

/-- The ground-ring tensor bifunctor on the possibly different carrier universes of two cochain
DGAs. -/
@[stacks 065W "ground-ring tensor bifunctor for the DGA tensor product"]
abbrev baseBifunctor :
    ModuleCat.{v} R ⥤ ModuleCat.{w} R ⥤ ModuleCat.{max v w} R :=
  ModuleCat.TensorProduct.functor.{u, v, w} R

/-- The ground-ring tensor product of two homogeneous terms in possibly different carrier
universes. -/
@[stacks 065W "homogeneous module tensor for the DGA tensor product"]
abbrev baseTensor (M : ModuleCat.{v₁} R) (N : ModuleCat.{v₂} R) :
    ModuleCat.{max v₁ v₂} R :=
  ModuleCat.TensorProduct.obj R M N

/-- The canonical total tensor complex underlying the tensor product DGA. -/
@[stacks 065W "total tensor complex underlying the DGA tensor product"]
abbrev complex : CochainComplex (ModuleCat.{max v w} R) ℤ :=
  HomologicalComplex.mapBifunctor A.toCochainComplex B.toCochainComplex
    (baseBifunctor (R := R)) (up ℤ)

/-- Include one homogeneous tensor summand into a specified total degree. -/
@[stacks 065W "homogeneous summand inclusion for the DGA tensor product"]
abbrev summandInclusion (p q n : ℤ) (h : p + q = n) :
    baseTensor (R := R) (A.X p) (B.X q) ⟶ (complex A B).X n :=
  ιMapBifunctor A.toCochainComplex B.toCochainComplex (baseBifunctor (R := R))
    (up ℤ) p q n h

/-- Homogeneous DGA multiplication as a morphism out of a module tensor product. -/
@[stacks 065W "homogeneous multiplication map for the DGA tensor product"]
abbrev mulHom (C : CochainDGAlgebra.{u, v} R) (p q : ℤ) :
    baseTensor (R := R) (C.X p) (C.X q) ⟶ C.X (p + q) :=
  ModuleCat.TensorProduct.lift R (C.mul p q)

/-- The four-factor shuffle which exchanges the two middle homogeneous factors and inserts the
Koszul sign. -/
@[stacks 065W "Koszul shuffle for the DGA tensor product"]
def koszulShuffle (p q p' q' : ℤ) :
    baseTensor (R := R)
        (baseTensor (R := R) (A.X p) (B.X q))
        (baseTensor (R := R) (A.X p') (B.X q')) ⟶
      baseTensor (R := R)
        (baseTensor (R := R) (A.X p) (A.X p'))
        (baseTensor (R := R) (B.X q) (B.X q')) :=
  ModuleCat.TensorProduct.koszulShuffle R
    (A.X p) (B.X q) (A.X p') (B.X q') q p'

/-- The Koszul product on four fixed homogeneous summands. -/
@[stacks 065W "homogeneous Koszul product component"]
def mulComponent (p q p' q' : ℤ) :
    baseTensor (R := R)
        (baseTensor (R := R) (A.X p) (B.X q))
        (baseTensor (R := R) (A.X p') (B.X q')) ⟶
      (complex A B).X ((p + q) + (p' + q')) :=
  koszulShuffle A B p q p' q' ≫
    ModuleCat.TensorProduct.map R (mulHom A p p') (mulHom B q q') ≫
      summandInclusion A B (p + p') (q + q') ((p + q) + (p' + q'))
        (mulTotalDegree p q p' q')

/-- The fixed-summand product, curried as a bilinear map. -/
@[stacks 065W "curried homogeneous multiplication for the DGA tensor product"]
abbrev mulCurried (p q p' q' : ℤ) :
    (baseTensor (R := R) (A.X p) (B.X q) : Type (max v w)) →ₗ[R]
      (baseTensor (R := R) (A.X p') (B.X q') : Type (max v w)) →ₗ[R]
      (complex A B).X ((p + q) + (p' + q')) :=
  _root_.TensorProduct.curry (mulComponent A B p q p' q').hom

/-- The target objects in a right-multiplication summand agree after total-degree transport. -/
theorem rightMulTargetEq (n m p q : ℤ) (hpq : p + q = n)
    (p' q' : ℤ) (hp'q' : (up ℤ).π (up ℤ) (up ℤ) (p', q') = m) :
    (complex A B).X ((p + q) + (p' + q')) = (complex A B).X (n + m) := sorry

/-- Right multiplication by an element of one fixed tensor summand. -/
def rightMulComponent (n m p q : ℤ) (hpq : p + q = n)
    (x : baseTensor (R := R) (A.X p) (B.X q)) (p' q' : ℤ)
    (hp'q' : (up ℤ).π (up ℤ) (up ℤ) (p', q') = m) :
    baseTensor (R := R) (A.X p') (B.X q') ⟶ (complex A B).X (n + m) :=
  ModuleCat.ofHom (mulCurried A B p q p' q' x) ≫
    eqToHom (rightMulTargetEq A B n m p q hpq p' q' hp'q')

/-- The summand family defining right multiplication on a total degree. -/
abbrev rightMulFamily (n m p q : ℤ) (hpq : p + q = n)
    (x : baseTensor (R := R) (A.X p) (B.X q)) (p' q' : ℤ)
    (hp'q' : (up ℤ).π (up ℤ) (up ℤ) (p', q') = m) :
    baseTensor (R := R) (A.X p') (B.X q') ⟶ (complex A B).X (n + m) :=
  rightMulComponent A B n m p q hpq x p' q' hp'q'

/-- Right multiplication descended from all summands in the right total degree. -/
def rightMulDesc (n m p q : ℤ) (hpq : p + q = n)
    (x : baseTensor (R := R) (A.X p) (B.X q)) :
    (complex A B).X m ⟶ (complex A B).X (n + m) :=
  mapBifunctorDesc (K₁ := A.toCochainComplex) (K₂ := B.toCochainComplex)
    (F := baseBifunctor (R := R)) (c := up ℤ)
    (rightMulFamily A B n m p q hpq x)

/-- Descended right multiplication is additive in the fixed left input. -/
theorem rightMulDesc_add (n m p q : ℤ) (hpq : p + q = n)
    (x y : baseTensor (R := R) (A.X p) (B.X q)) :
    (rightMulDesc A B n m p q hpq (x + y)).hom =
      (rightMulDesc A B n m p q hpq x).hom +
        (rightMulDesc A B n m p q hpq y).hom := sorry

/-- Descended right multiplication is linear in the fixed left input. -/
theorem rightMulDesc_smul (n m p q : ℤ) (hpq : p + q = n)
    (r : R) (x : baseTensor (R := R) (A.X p) (B.X q)) :
    (rightMulDesc A B n m p q hpq (r • x)).hom =
      r • (rightMulDesc A B n m p q hpq x).hom := sorry

/-- Right multiplication as a linear map on one left summand. -/
def rightMulOnSummand (n m p q : ℤ) (hpq : p + q = n) :
    baseTensor (R := R) (A.X p) (B.X q) ⟶ ModuleCat.of R
      (((complex A B).X m) →ₗ[R] (complex A B).X (n + m)) :=
  ModuleCat.ofHom
    { toFun := fun x ↦ (rightMulDesc A B n m p q hpq x).hom
      map_add' := rightMulDesc_add A B n m p q hpq
      map_smul' := rightMulDesc_smul A B n m p q hpq }

/-- The summand family defining multiplication from a total left degree. -/
abbrev mulFamily (n m p q : ℤ) (hpq : p + q = n) :
    baseTensor (R := R) (A.X p) (B.X q) ⟶ ModuleCat.of R
      (((complex A B).X m) →ₗ[R] (complex A B).X (n + m)) :=
  rightMulOnSummand A B n m p q hpq

/-- Multiplication descended from every summand of the left total degree. -/
def mulDesc (n m : ℤ) :
    (complex A B).X n ⟶ ModuleCat.of R
      (((complex A B).X m) →ₗ[R] (complex A B).X (n + m)) :=
  mapBifunctorDesc (K₁ := A.toCochainComplex) (K₂ := B.toCochainComplex)
    (F := baseBifunctor (R := R)) (c := up ℤ) (mulFamily A B n m)

/-- The unit in total degree zero. -/
@[stacks 065W "unit of the total tensor complex"]
def one : (complex A B).X 0 :=
  (summandInclusion A B 0 0 0 zeroTotalDegree).hom (A.one ⊗ₜ[R] B.one)

/-- Koszul multiplication on the total tensor complex. -/
@[stacks 065W "multiplication on the total tensor complex"]
def mul (n m : ℤ) :
    (complex A B).X n →ₗ[R] (complex A B).X m →ₗ[R] (complex A B).X (n + m) :=
  (mulDesc A B n m).hom

/-- Koszul multiplication on the total tensor complex is associative. -/
@[stacks 065W "associativity of total Koszul multiplication"]
theorem mul_assoc (i j k : ℤ) (a : (complex A B).X i) (b : (complex A B).X j)
    (c : (complex A B).X k) :
    cast (congrArg (fun n : ℤ ↦ ((complex A B).X n : Type (max v w))) (add_assoc i j k))
      (mul A B (i + j) k (mul A B i j a b) c) =
        mul A B i (j + k) a (mul A B j k b c) := sorry

/-- The pure tensor of the units is a left unit for Koszul multiplication. -/
@[stacks 065W "left unit of total Koszul multiplication"]
theorem one_mul (n : ℤ) (a : (complex A B).X n) :
    cast (congrArg (fun i : ℤ ↦ ((complex A B).X i : Type (max v w))) (zero_add n))
      (mul A B 0 n (one A B) a) = a := sorry

/-- The pure tensor of the units is a right unit for Koszul multiplication. -/
@[stacks 065W "right unit of total Koszul multiplication"]
theorem mul_one (n : ℤ) (a : (complex A B).X n) :
    cast (congrArg (fun i : ℤ ↦ ((complex A B).X i : Type (max v w))) (add_zero n))
      (mul A B n 0 a (one A B)) = a := sorry

/-- Koszul multiplication satisfies the cochain Leibniz rule. -/
@[stacks 065W "Leibniz rule for total Koszul multiplication"]
theorem leibniz (n m : ℤ) (a : (complex A B).X n) (b : (complex A B).X m) :
    (complex A B).d (n + m) (n + m + 1) (mul A B n m a b) =
      cast (congrArg (fun i : ℤ ↦ ((complex A B).X i : Type (max v w)))
          (CochainDGAlgebra.leftLeibnizIndex n m))
          (mul A B (n + 1) m ((complex A B).d n (n + 1) a) b) +
        n.negOnePow •
          cast (congrArg (fun i : ℤ ↦ ((complex A B).X i : Type (max v w)))
            (CochainDGAlgebra.rightLeibnizIndex n m))
            (mul A B n (m + 1) a ((complex A B).d m (m + 1) b)) := sorry

end Tensor

/-- Definition 22.3.4 (065W): the Koszul tensor product of cochain differential graded
algebras, with output carrier in the maximum of the two input carrier universes. -/
@[reducible, stacks 065W]
def tensorProduct (A : CochainDGAlgebra.{u, v} R) (B : CochainDGAlgebra.{u, w} R) :
    CochainDGAlgebra.{u, max v w} R where
  toCochainComplex := Tensor.complex A B
  one := Tensor.one A B
  mul := Tensor.mul A B
  mul_assoc := Tensor.mul_assoc A B
  one_mul := Tensor.one_mul A B
  mul_one := Tensor.mul_one A B
  leibniz := Tensor.leibniz A B

/- The reusable notation for the Koszul tensor product of cochain DGAs over `R`. -/
set_option quotPrecheck false in
scoped[TensorProduct] notation:70 A:70 " ⊗[" R:70 "] " B:71 =>
  @CochainDGAlgebra.tensorProduct R _ A B

variable (A : CochainDGAlgebra.{u, v} R) (B : CochainDGAlgebra.{u, w} R)

/-- The tensor-product DGA has the canonical total tensor complex underneath. -/
@[stacks 065X, simp]
theorem tensorProduct_toCochainComplex :
    (A ⊗[R] B).toCochainComplex = Tensor.complex A B := sorry

/-- The degree-`n` object of the tensor-product DGA is the degree-`n` object of the total tensor
complex. -/
@[simp]
theorem tensorProduct_X (n : ℤ) :
    (A ⊗[R] B).X n = (Tensor.complex A B).X n := sorry

/-- The tensor-product DGA unit is the included pure tensor of the two units. -/
@[simp]
theorem tensorProduct_one :
    (A ⊗[R] B).one =
      (Tensor.summandInclusion A B 0 0 0 Tensor.zeroTotalDegree).hom
        (A.one ⊗ₜ[R] B.one) := sorry

/-- The bundled tensor-product multiplication is the descended Koszul multiplication. -/
@[simp]
theorem tensorProduct_mul (n m : ℤ) :
    (A ⊗[R] B).mul n m = Tensor.mul A B n m := sorry

/-- On homogeneous pure tensors, multiplication swaps the middle factors with the Koszul sign. -/
theorem tensorProduct_mul_pure (p q p' q' : ℤ)
    (a : A.X p) (b : B.X q) (a' : A.X p') (b' : B.X q') :
    (A ⊗[R] B).mul (p + q) (p' + q')
        ((Tensor.summandInclusion A B p q (p + q)
          (Tensor.totalDegree p q)).hom (a ⊗ₜ[R] b))
        ((Tensor.summandInclusion A B p' q' (p' + q')
          (Tensor.totalDegree p' q')).hom (a' ⊗ₜ[R] b')) =
      ((q * p').negOnePow : R) •
        ((Tensor.summandInclusion A B (p + p') (q + q') ((p + q) + (p' + q'))
          (Tensor.mulTotalDegree p q p' q')).hom
          ((A.mul p p' a a') ⊗ₜ[R] (B.mul q q' b b'))) := sorry

/-- The differential on a homogeneous tensor summand is the signed sum of the two factor
differentials. -/
theorem tensorProduct_d_on_summand (p q : ℤ) :
    Tensor.summandInclusion A B p q (p + q) (Tensor.totalDegree p q) ≫
        (A ⊗[R] B).d (p + q) =
      ModuleCat.TensorProduct.map R (A.d p) (𝟙 (B.X q)) ≫
          Tensor.summandInclusion A B (p + 1) q (p + q + 1)
            (Tensor.dLeftTotalDegree p q) +
        p.negOnePow •
          (ModuleCat.TensorProduct.map R (𝟙 (A.X p)) (B.d q) ≫
            Tensor.summandInclusion A B p (q + 1) (p + q + 1)
              (Tensor.dRightTotalDegree p q)) := sorry

namespace Tensor

/-- The summand containing a degree-`i` element of `A` and the unit of `B` has total
degree `i` in `A ⊗[R] B`. -/
theorem leftFactorDegree (i : ℤ) :
    (up ℤ).π (up ℤ) (up ℤ) (i, 0) = i := sorry

/-- Include a homogeneous element of `A` in the left factor of `A ⊗[R] B`. -/
def leftFactor {i : ℤ} (a : A.X i) :
    (CochainDGAlgebra.tensorProduct A B).X i :=
  (summandInclusion A B i 0 i (leftFactorDegree i)).hom (a ⊗ₜ[R] B.one)

/-- The left-factor inclusion `A.X i ⟶ (A ⊗[R] B).X i` as an `R`-linear map. -/
def leftFactorLinearMap (i : ℤ) : A.X i →ₗ[R]
    (CochainDGAlgebra.tensorProduct A B).X i where
  toFun := leftFactor A B
  map_add' := sorry
  map_smul' := sorry

/-- The canonical DGA homomorphism `A ⟶ A ⊗[R] B` obtained by tensoring with the
unit of `B`. -/
@[stacks 0BYZ "left factor of a tensor product differential graded algebra"]
def leftFactorHom : CochainDGAlgebra.Hom A
    (CochainDGAlgebra.tensorProduct A B) where
  map := leftFactorLinearMap A B
  comm_d := sorry
  map_one := sorry
  map_mul := sorry

/-- The left-factor DGA homomorphism evaluates by tensoring with the unit of `B`. -/
@[simp]
theorem leftFactorHom_apply (i : ℤ) (a : A.X i) :
    leftFactorHom A B i a = leftFactor A B a := sorry

/-- The summand containing the unit of `A` and a degree-`j` element of `B` has total
degree `j` in `A ⊗[R] B`. -/
theorem rightFactorDegree (j : ℤ) :
    (up ℤ).π (up ℤ) (up ℤ) (0, j) = j := sorry

/-- Include a homogeneous element of `B` in the right factor of `A ⊗[R] B`. -/
def rightFactor {j : ℤ} (b : B.X j) :
    (CochainDGAlgebra.tensorProduct A B).X j :=
  (summandInclusion A B 0 j j (rightFactorDegree j)).hom (A.one ⊗ₜ[R] b)

/-- The right-factor inclusion `B.X j ⟶ (A ⊗[R] B).X j` as an `R`-linear map. -/
def rightFactorLinearMap (j : ℤ) : B.X j →ₗ[R]
    (CochainDGAlgebra.tensorProduct A B).X j where
  toFun := rightFactor A B
  map_add' := sorry
  map_smul' := sorry

/-- The canonical DGA homomorphism `B ⟶ A ⊗[R] B` obtained by tensoring with the
unit of `A`. -/
@[stacks 0BZ4 "right factor of a tensor product differential graded algebra"]
def rightFactorHom : CochainDGAlgebra.Hom B
    (CochainDGAlgebra.tensorProduct A B) where
  map := rightFactorLinearMap A B
  comm_d := sorry
  map_one := sorry
  map_mul := sorry

/-- The right-factor DGA homomorphism evaluates by tensoring with the unit of `A`. -/
@[simp]
theorem rightFactorHom_apply (j : ℤ) (b : B.X j) :
    rightFactorHom A B j b = rightFactor A B b := sorry

end Tensor

namespace Tensor

variable (A : CochainDGAlgebra.{u, v} R)

/-- Multiplication on one homogeneous summand of the total complex `A ⊗[R] A`, transported
to the specified total degree. -/
def multiplicationComponent (p q n : ℤ)
    (h : (up ℤ).π (up ℤ) (up ℤ) (p, q) = n) :
    baseTensor (R := R) (A.X p) (A.X q) ⟶ A.X n :=
  mulHom A p q ≫ eqToHom
    (congrArg A.X ((totalDegree p q).symm.trans h))

/-- Multiplication in a cochain DGA, bundled as the canonical cochain map
`A.toCochainComplex ⊗ A.toCochainComplex ⟶ A.toCochainComplex`. -/
@[stacks 0BZ4 "multiplication map of a cochain differential graded algebra"]
noncomputable def multiplicationMap : complex A A ⟶ A.toCochainComplex where
  f n := mapBifunctorDesc (K₁ := A.toCochainComplex) (K₂ := A.toCochainComplex)
    (F := baseBifunctor (R := R)) (c := up ℤ)
    (fun p q h ↦ multiplicationComponent A p q n h)
  comm' := sorry

end Tensor

namespace Hom

variable {A A' C : CochainDGAlgebra.{u, v} R}
  {B B' C' : CochainDGAlgebra.{u, w} R}

/-- Tensoring two DGA homomorphisms preserves the tensor-product unit. -/
theorem tensorProduct_map_one (f : Hom A A') (g : Hom B B') :
    (HomologicalComplex.mapBifunctorMap f.toCochainMap g.toCochainMap
      (Tensor.baseBifunctor (R := R)) (up ℤ)).f 0 (Tensor.one A B) =
        Tensor.one A' B' := sorry

/-- Tensoring two DGA homomorphisms preserves Koszul multiplication. -/
theorem tensorProduct_map_mul (f : Hom A A') (g : Hom B B') (n m : ℤ)
    (a : (Tensor.complex A B).X n) (b : (Tensor.complex A B).X m) :
    (HomologicalComplex.mapBifunctorMap f.toCochainMap g.toCochainMap
      (Tensor.baseBifunctor (R := R)) (up ℤ)).f (n + m)
        (Tensor.mul A B n m a b) =
      Tensor.mul A' B' n m
        ((HomologicalComplex.mapBifunctorMap f.toCochainMap g.toCochainMap
          (Tensor.baseBifunctor (R := R)) (up ℤ)).f n a)
        ((HomologicalComplex.mapBifunctorMap f.toCochainMap g.toCochainMap
          (Tensor.baseBifunctor (R := R)) (up ℤ)).f m b) := sorry

/-- The tensor product of two cochain-DGA homomorphisms. -/
@[stacks 065W "tensor product of cochain-DGA homomorphisms"]
noncomputable def tensorProduct (f : Hom A A') (g : Hom B B') :
    Hom (CochainDGAlgebra.tensorProduct A B) (CochainDGAlgebra.tensorProduct A' B') where
  map n := ((HomologicalComplex.mapBifunctorMap f.toCochainMap g.toCochainMap
    (Tensor.baseBifunctor (R := R)) (up ℤ)).f n).hom
  comm_d := sorry
  map_one := tensorProduct_map_one f g
  map_mul := tensorProduct_map_mul f g

/-- The underlying cochain map of a tensor-product DGA homomorphism is the canonical tensor map. -/
@[simp]
theorem tensorProduct_toCochainMap (f : Hom A A') (g : Hom B B') :
    (tensorProduct f g).toCochainMap =
      HomologicalComplex.mapBifunctorMap f.toCochainMap g.toCochainMap
        (Tensor.baseBifunctor (R := R)) (up ℤ) := sorry

/-- A tensor-product DGA homomorphism acts by the canonical tensor map in each degree. -/
@[simp]
theorem tensorProduct_apply (f : Hom A A') (g : Hom B B') (n : ℤ)
    (x : (Tensor.complex A B).X n) :
    tensorProduct f g n x =
      (HomologicalComplex.mapBifunctorMap f.toCochainMap g.toCochainMap
        (Tensor.baseBifunctor (R := R)) (up ℤ)).f n x := sorry

/-- A tensor-product DGA homomorphism maps an included pure tensor componentwise. -/
@[simp]
theorem tensorProduct_apply_pure (f : Hom A A') (g : Hom B B') (p q : ℤ)
    (a : A.X p) (b : B.X q) :
    tensorProduct f g (p + q)
        ((Tensor.summandInclusion A B p q (p + q)
          (Tensor.totalDegree p q)).hom (a ⊗ₜ[R] b)) =
      (Tensor.summandInclusion A' B' p q (p + q)
        (Tensor.totalDegree p q)).hom (f p a ⊗ₜ[R] g q b) := sorry

/-- Tensoring identity DGA homomorphisms gives the identity. -/
@[simp]
theorem tensorProduct_id (A : CochainDGAlgebra.{u, v} R)
    (B : CochainDGAlgebra.{u, w} R) :
    tensorProduct (Hom.id A) (Hom.id B) = Hom.id (CochainDGAlgebra.tensorProduct A B) := sorry

/-- Tensor products of DGA homomorphisms preserve composition in both variables. -/
@[simp]
theorem tensorProduct_comp
    (f₂ : Hom A' C) (f₁ : Hom A A') (g₂ : Hom B' C') (g₁ : Hom B B') :
    tensorProduct (Hom.comp f₂ f₁) (Hom.comp g₂ g₁) =
      Hom.comp (tensorProduct f₂ g₂) (tensorProduct f₁ g₁) := sorry

end Hom

namespace Tensor

/-- The tensor product is a bifunctor in the two cochain-DGA variables, with the output carrier
universe formed by `max v w`. -/
@[stacks 065W "bifunctorial tensor product of cochain DGAs"]
noncomputable def tensorFunctor :
    CochainDGAlgebra.{u, v} R ⥤
      CochainDGAlgebra.{u, w} R ⥤ CochainDGAlgebra.{u, max v w} R where
  obj A :=
    { obj := fun B ↦ CochainDGAlgebra.tensorProduct A B
      map := fun f ↦ CochainDGAlgebra.Hom.tensorProduct (CochainDGAlgebra.Hom.id A) f
      map_id := sorry
      map_comp := sorry }
  map f :=
    { app := fun B ↦ CochainDGAlgebra.Hom.tensorProduct f (CochainDGAlgebra.Hom.id B)
      naturality := sorry }
  map_id := sorry
  map_comp := sorry

/-- The tensor bifunctor acts on objects by the canonical DGA tensor product. -/
@[simp]
theorem tensorFunctor_obj (A : CochainDGAlgebra.{u, v} R)
    (B : CochainDGAlgebra.{u, w} R) :
    ((tensorFunctor (R := R)).obj A).obj B = CochainDGAlgebra.tensorProduct A B := sorry

/-- The tensor bifunctor acts on a morphism in its second variable by the tensor homomorphism. -/
@[simp]
theorem tensorFunctor_obj_map (A : CochainDGAlgebra.{u, v} R)
    {B B' : CochainDGAlgebra.{u, w} R} (g : B ⟶ B') :
    ((tensorFunctor (R := R)).obj A).map g =
      CochainDGAlgebra.Hom.tensorProduct (CochainDGAlgebra.Hom.id A) g := sorry

/-- The tensor bifunctor acts on a morphism in its first variable by the tensor homomorphism. -/
@[simp]
theorem tensorFunctor_map_app {A A' : CochainDGAlgebra.{u, v} R}
    (f : A ⟶ A') (B : CochainDGAlgebra.{u, w} R) :
    ((tensorFunctor (R := R)).map f).app B =
      CochainDGAlgebra.Hom.tensorProduct f (CochainDGAlgebra.Hom.id B) := sorry

end Tensor

end CochainDGAlgebra
