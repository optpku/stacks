/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.Nonnegative
public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.Semilinear

/-!
# Restriction of scalars for chain differential graded algebras

Restriction of scalars is constructed on the underlying homological complex with Mathlib's
`ModuleCat.restrictScalars`. The multiplication and unit retain their original functions. A
semilinear chain-DGA morphism then becomes an ordinary morphism into the restricted target.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe uR uS uB

namespace ChainDGAlgebra

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]

/-- One homogeneous component of a chain DGA over `S`, regarded as an `R`-module along
`sigma : R →+* S`. -/
abbrev restrictScalarsPiece (sigma : R →+* S) (B : ChainDGAlgebra.{uS, uB} S) (n : ℤ) :
    ModuleCat.{uB} R :=
  (ModuleCat.restrictScalars sigma).obj (B.X n)

/-- The underlying chain complex after restriction of scalars. -/
abbrev restrictScalarsComplex (sigma : R →+* S) (B : ChainDGAlgebra.{uS, uB} S) :
    ChainComplex (ModuleCat.{uB} R) ℤ :=
  ((ModuleCat.restrictScalars sigma).mapHomologicalComplex (ComplexShape.down ℤ)).obj
    B.toChainComplex

/-- The original homogeneous multiplication is additive in its left argument after restriction
of scalars. -/
theorem restrictScalarsMul_add_left (sigma : R →+* S) (B : ChainDGAlgebra.{uS, uB} S)
    (n m : ℤ) (x y : B.restrictScalarsPiece sigma n)
    (z : B.restrictScalarsPiece sigma m) :
    B.mul n m (x + y) z = B.mul n m x z + B.mul n m y z := sorry

/-- The original homogeneous multiplication is `R`-linear in its left argument after
restriction of scalars. -/
theorem restrictScalarsMul_smul_left (sigma : R →+* S) (B : ChainDGAlgebra.{uS, uB} S)
    (n m : ℤ) (r : R) (x : B.restrictScalarsPiece sigma n)
    (y : B.restrictScalarsPiece sigma m) :
    B.mul n m (r • x) y = sigma r • B.mul n m x y := sorry

/-- The original homogeneous multiplication is additive in its right argument after restriction
of scalars. -/
theorem restrictScalarsMul_add_right (sigma : R →+* S) (B : ChainDGAlgebra.{uS, uB} S)
    (n m : ℤ) (x : B.restrictScalarsPiece sigma n)
    (y z : B.restrictScalarsPiece sigma m) :
    B.mul n m x (y + z) = B.mul n m x y + B.mul n m x z := sorry

/-- The original homogeneous multiplication is `R`-linear in its right argument after
restriction of scalars. -/
theorem restrictScalarsMul_smul_right (sigma : R →+* S) (B : ChainDGAlgebra.{uS, uB} S)
    (n m : ℤ) (r : R) (x : B.restrictScalarsPiece sigma n)
    (y : B.restrictScalarsPiece sigma m) :
    B.mul n m x (r • y) = sigma r • B.mul n m x y := sorry

/-- Homogeneous multiplication on the restriction of scalars. Its underlying function is the
original multiplication. -/
def restrictScalarsMul (sigma : R →+* S) (B : ChainDGAlgebra.{uS, uB} S) (n m : ℤ) :
    B.restrictScalarsPiece sigma n →ₗ[R]
      B.restrictScalarsPiece sigma m →ₗ[R]
        B.restrictScalarsPiece sigma (n + m) :=
  LinearMap.mk₂ R (fun x y ↦ B.mul n m x y)
    (B.restrictScalarsMul_add_left sigma n m)
    (B.restrictScalarsMul_smul_left sigma n m)
    (B.restrictScalarsMul_add_right sigma n m)
    (B.restrictScalarsMul_smul_right sigma n m)

/-- Restricted homogeneous multiplication remains associative. -/
theorem restrictScalars_mul_assoc (sigma : R →+* S) (B : ChainDGAlgebra.{uS, uB} S)
    (i j k : ℤ) (x : B.restrictScalarsPiece sigma i)
    (y : B.restrictScalarsPiece sigma j) (z : B.restrictScalarsPiece sigma k) :
    cast (congrArg (fun n : ℤ ↦ (B.restrictScalarsPiece sigma n : Type uB))
      (add_assoc i j k))
        (B.restrictScalarsMul sigma (i + j) k
          (B.restrictScalarsMul sigma i j x y) z) =
      B.restrictScalarsMul sigma i (j + k) x
        (B.restrictScalarsMul sigma j k y z) := sorry

/-- The original unit remains a left unit after restriction of scalars. -/
theorem restrictScalars_one_mul (sigma : R →+* S) (B : ChainDGAlgebra.{uS, uB} S)
    (n : ℤ) (x : B.restrictScalarsPiece sigma n) :
    cast (congrArg (fun i : ℤ ↦ (B.restrictScalarsPiece sigma i : Type uB))
      (zero_add n)) (B.restrictScalarsMul sigma 0 n B.one x) = x := sorry

/-- The original unit remains a right unit after restriction of scalars. -/
theorem restrictScalars_mul_one (sigma : R →+* S) (B : ChainDGAlgebra.{uS, uB} S)
    (n : ℤ) (x : B.restrictScalarsPiece sigma n) :
    cast (congrArg (fun i : ℤ ↦ (B.restrictScalarsPiece sigma i : Type uB))
      (add_zero n)) (B.restrictScalarsMul sigma n 0 x B.one) = x := sorry

/-- The original differential and multiplication satisfy the chain Leibniz rule after
restriction of scalars. -/
theorem restrictScalars_leibniz (sigma : R →+* S) (B : ChainDGAlgebra.{uS, uB} S)
    (n m : ℤ) (x : B.restrictScalarsPiece sigma n)
    (y : B.restrictScalarsPiece sigma m) :
    (B.restrictScalarsComplex sigma).d (n + m) (n + m - 1)
        (B.restrictScalarsMul sigma n m x y) =
      cast (congrArg (fun i : ℤ ↦ (B.restrictScalarsPiece sigma i : Type uB))
        (ChainDGAlgebra.leftLeibnizIndex n m))
          (B.restrictScalarsMul sigma (n - 1) m
            ((B.restrictScalarsComplex sigma).d n (n - 1) x) y) +
        n.negOnePow •
          cast (congrArg (fun i : ℤ ↦ (B.restrictScalarsPiece sigma i : Type uB))
            (ChainDGAlgebra.rightLeibnizIndex n m))
              (B.restrictScalarsMul sigma n (m - 1) x
                ((B.restrictScalarsComplex sigma).d m (m - 1) y)) := sorry

/-- Restrict a chain differential graded algebra along a homomorphism of commutative rings. -/
@[stacks 09PQ "restriction of scalars for chain differential graded algebras"]
def restrictScalars (sigma : R →+* S) (B : ChainDGAlgebra.{uS, uB} S) :
    ChainDGAlgebra.{uR, uB} R where
  toChainComplex := B.restrictScalarsComplex sigma
  mul := B.restrictScalarsMul sigma
  one := B.one
  mul_assoc := B.restrictScalars_mul_assoc sigma
  one_mul := B.restrictScalars_one_mul sigma
  mul_one := B.restrictScalars_mul_one sigma
  leibniz := B.restrictScalars_leibniz sigma

/-- A homogeneous component of the restricted chain DGA is the corresponding restricted
`ModuleCat` object. -/
@[simp]
theorem restrictScalars_X (sigma : R →+* S) (B : ChainDGAlgebra.{uS, uB} S) (n : ℤ) :
    (B.restrictScalars sigma).X n = B.restrictScalarsPiece sigma n := sorry

/-- Restricted multiplication evaluates by the original homogeneous multiplication. -/
@[simp]
theorem restrictScalars_mul (sigma : R →+* S) (B : ChainDGAlgebra.{uS, uB} S)
    (n m : ℤ) (x : (B.restrictScalars sigma).X n)
    (y : (B.restrictScalars sigma).X m) :
    (B.restrictScalars sigma).mul n m x y = B.mul n m x y := sorry

/-- The unit of a restricted chain DGA is the original unit. -/
@[simp]
theorem restrictScalars_one (sigma : R →+* S) (B : ChainDGAlgebra.{uS, uB} S) :
    (B.restrictScalars sigma).one = B.one := sorry

/-- The differential of a restricted chain DGA is the original differential on elements. -/
@[simp]
theorem restrictScalars_d (sigma : R →+* S) (B : ChainDGAlgebra.{uS, uB} S)
    (n : ℤ) (x : (B.restrictScalars sigma).X n) :
    (B.restrictScalars sigma).d n x = B.d n x := sorry

/-- Graded commutativity is preserved canonically by restriction of scalars. -/
@[stacks 09PQ "graded commutativity under restriction of scalars"]
instance IsCommutative.restrictScalars {sigma : R →+* S} {B : ChainDGAlgebra.{uS, uB} S}
    [B.IsCommutative] : (B.restrictScalars sigma).IsCommutative := sorry

/-- Strict graded commutativity is preserved canonically by restriction of scalars. -/
@[stacks 09PQ "strict graded commutativity under restriction of scalars"]
instance IsStrictlyCommutative.restrictScalars
    {sigma : R →+* S} {B : ChainDGAlgebra.{uS, uB} S}
    [B.IsStrictlyCommutative] : (B.restrictScalars sigma).IsStrictlyCommutative := sorry

/-- Nonnegative support is preserved canonically by restriction of scalars. -/
instance IsNonnegative.restrictScalars {sigma : R →+* S} {B : ChainDGAlgebra.{uS, uB} S}
    [B.IsNonnegative] : (B.restrictScalars sigma).IsNonnegative := sorry

namespace SemilinearHom

variable {sigma : R →+* S}
variable {A : ChainDGAlgebra.{uR, uB} R} {B : ChainDGAlgebra.{uS, uB} S}

/-!
The conversion below intentionally uses the same carrier universe for `A` and `B`.
Mathlib's `ModuleCat.semilinearMapAddEquiv` and the current `ChainDGAlgebra.Hom` both compare
module objects in one fixed `ModuleCat` universe; the unrestricted `SemilinearHom` owner itself
remains universe-polymorphic in its source and target carriers.
-/

/-- The component of a semilinear morphism as an ordinary linear map into the restriction of
scalars of its target. -/
def toRestrictScalarsComponent (f : SemilinearHom sigma A B) (n : ℤ) :
    A.X n ⟶ (B.restrictScalars sigma).X n :=
  ModuleCat.semilinearMapAddEquiv sigma (A.X n) (B.X n) (f.map n)

/-- The restricted component acts by the original semilinear function. -/
@[simp]
theorem toRestrictScalarsComponent_apply (f : SemilinearHom sigma A B)
    (n : ℤ) (x : A.X n) : f.toRestrictScalarsComponent n x = f n x := sorry

/-- The restricted components commute with every differential of the chain-complex shape. -/
theorem toRestrictScalarsComponent_comm (f : SemilinearHom sigma A B)
    (i j : ℤ) (hij : (ComplexShape.down ℤ).Rel i j) :
    f.toRestrictScalarsComponent i ≫ (B.restrictScalars sigma).toChainComplex.d i j =
      A.toChainComplex.d i j ≫ f.toRestrictScalarsComponent j := sorry

/-- The chain map obtained from a semilinear morphism by restricting scalars in its target. -/
def toRestrictScalarsChainMap (f : SemilinearHom sigma A B) :
    A.toChainComplex ⟶ (B.restrictScalars sigma).toChainComplex where
  f := f.toRestrictScalarsComponent
  comm' := f.toRestrictScalarsComponent_comm

/-- The components of the restricted chain map are the restricted semilinear components. -/
@[simp]
theorem toRestrictScalarsChainMap_f (f : SemilinearHom sigma A B) (n : ℤ) :
    f.toRestrictScalarsChainMap.f n = f.toRestrictScalarsComponent n := sorry

/-- The restricted chain map preserves the unit. -/
theorem toRestrictScalarsChainMap_one (f : SemilinearHom sigma A B) :
    f.toRestrictScalarsChainMap.f 0 A.one = (B.restrictScalars sigma).one := sorry

/-- The restricted chain map preserves homogeneous multiplication. -/
theorem toRestrictScalarsChainMap_mul (f : SemilinearHom sigma A B)
    (n m : ℤ) (x : A.X n) (y : A.X m) :
    f.toRestrictScalarsChainMap.f (n + m) (A.mul n m x y) =
      (B.restrictScalars sigma).mul n m
        (f.toRestrictScalarsChainMap.f n x) (f.toRestrictScalarsChainMap.f m y) := sorry

/-- Regard a semilinear chain-DGA morphism as an ordinary morphism into the restriction of
scalars of its target. -/
@[stacks 09PQ "semilinear chain-DGA morphism as a restricted-scalar morphism"]
def toRestrictScalarsHom (f : SemilinearHom sigma A B) :
    ChainDGAlgebra.Hom A (B.restrictScalars sigma) where
  toChainMap := f.toRestrictScalarsChainMap
  map_one := f.toRestrictScalarsChainMap_one
  map_mul := f.toRestrictScalarsChainMap_mul

/-- Restricting the target scalars does not change the pointwise action of a semilinear
chain-DGA morphism. -/
@[simp]
theorem toRestrictScalarsHom_apply (f : SemilinearHom sigma A B)
    (n : ℤ) (x : A.X n) : f.toRestrictScalarsHom n x = f n x := sorry

/-- An ordinary component into a restricted target, regarded as a semilinear map into the
original target. -/
def ofRestrictScalarsComponent (f : ChainDGAlgebra.Hom A (B.restrictScalars sigma)) (n : ℤ) :
    A.X n →ₛₗ[sigma] B.X n :=
  (ModuleCat.semilinearMapAddEquiv sigma (A.X n) (B.X n)).symm (f.toChainMap.f n)

/-- Recovering a semilinear component does not change the underlying function. -/
@[simp]
theorem ofRestrictScalarsComponent_apply
    (f : ChainDGAlgebra.Hom A (B.restrictScalars sigma)) (n : ℤ) (x : A.X n) :
    ofRestrictScalarsComponent f n x = f n x := sorry

/-- Components recovered from a restricted-target morphism commute with the original
differentials. -/
theorem ofRestrictScalarsComponent_map_d
    (f : ChainDGAlgebra.Hom A (B.restrictScalars sigma)) (n : ℤ) (x : A.X n) :
    ofRestrictScalarsComponent f (n - 1) (A.d n x) =
      B.d n (ofRestrictScalarsComponent f n x) := sorry

/-- Components recovered from a restricted-target morphism preserve the original unit. -/
theorem ofRestrictScalarsComponent_map_one
    (f : ChainDGAlgebra.Hom A (B.restrictScalars sigma)) :
    ofRestrictScalarsComponent f 0 A.one = B.one := sorry

/-- Components recovered from a restricted-target morphism preserve homogeneous
multiplication. -/
theorem ofRestrictScalarsComponent_map_mul
    (f : ChainDGAlgebra.Hom A (B.restrictScalars sigma)) (n m : ℤ)
    (x : A.X n) (y : A.X m) :
    ofRestrictScalarsComponent f (n + m) (A.mul n m x y) =
      B.mul n m (ofRestrictScalarsComponent f n x)
        (ofRestrictScalarsComponent f m y) := sorry

/-- Regard an ordinary morphism into a restricted target as a semilinear chain-DGA morphism
into the original target. -/
def ofRestrictScalarsHom (f : ChainDGAlgebra.Hom A (B.restrictScalars sigma)) :
    SemilinearHom sigma A B where
  map := ofRestrictScalarsComponent f
  map_d := ofRestrictScalarsComponent_map_d f
  map_one := ofRestrictScalarsComponent_map_one f
  map_mul := ofRestrictScalarsComponent_map_mul f

/-- Recovering a semilinear morphism from a restricted-target morphism preserves its pointwise
action. -/
@[simp]
theorem ofRestrictScalarsHom_apply
    (f : ChainDGAlgebra.Hom A (B.restrictScalars sigma)) (n : ℤ) (x : A.X n) :
    ofRestrictScalarsHom f n x = f n x := sorry

/-- Converting a semilinear morphism to a restricted-target morphism and back is the identity. -/
@[simp]
theorem ofRestrictScalarsHom_toRestrictScalarsHom (f : SemilinearHom sigma A B) :
    ofRestrictScalarsHom f.toRestrictScalarsHom = f := sorry

/-- Converting a restricted-target morphism to a semilinear morphism and back is the identity. -/
@[simp]
theorem toRestrictScalarsHom_ofRestrictScalarsHom
    (f : ChainDGAlgebra.Hom A (B.restrictScalars sigma)) :
    (ofRestrictScalarsHom f).toRestrictScalarsHom = f := sorry

/-- Semilinear chain-DGA morphisms identify canonically with ordinary morphisms into the
restriction of scalars of the target. -/
@[stacks 09PQ "semilinear and restricted-scalar chain-DGA morphisms"]
def restrictScalarsHomEquiv :
    SemilinearHom sigma A B ≃ ChainDGAlgebra.Hom A (B.restrictScalars sigma) where
  toFun := toRestrictScalarsHom
  invFun := ofRestrictScalarsHom
  left_inv := ofRestrictScalarsHom_toRestrictScalarsHom
  right_inv := toRestrictScalarsHom_ofRestrictScalarsHom

end SemilinearHom

end ChainDGAlgebra
