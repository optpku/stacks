/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.RestrictScalars
public import ReasLib.RingTheory.DividedPowers.DifferentialGraded.Semilinear

/-!
# Restriction of scalars for divided-power chain DGAs

Restriction of scalars keeps every homogeneous carrier and every divided-power operation.  This
file records the changed scalar actions in a bundled divided-power chain DGA, makes the operation
data explicit, and identifies semilinear divided-power maps with ordinary maps into a restricted
target.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped DirectSum

universe uR uS uB

namespace DividedPowerChainAlgebra

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]

namespace RestrictScalars

/-- The nonnegative graded algebra underlying the scalar restriction of a divided-power chain
DGA. -/
abbrev graded (sigma : R →+* S)
    (B : DividedPowerChainAlgebra.{uS, uB} S) :
    NonnegGradedAlgebra.{uR, uB} R :=
  (B.toChainDGAlgebra.restrictScalars sigma).nonnegativePart

/-- The total divided-power operation on the restricted nonnegative graded algebra.  Its
underlying function is the original operation. -/
def gamma (sigma : R →+* S)
    (B : DividedPowerChainAlgebra.{uS, uB} S) (n : ℕ)
    (x : (graded sigma B).evenPositivePart) :
    (graded sigma B).evenPart :=
  B.gamma n x

/-- The positive-index divided-power operation on the restricted nonnegative graded algebra.
Its underlying function is the original positive operation. -/
def gammaPos (sigma : R →+* S)
    (B : DividedPowerChainAlgebra.{uS, uB} S) (n : ℕ+)
    (x : (graded sigma B).evenPositivePart) :
    (graded sigma B).evenPositivePart :=
  B.gamma.gammaPos n x

/-- Positive restricted divided powers agree with the total restricted operation after the
canonical inclusion. -/
theorem gamma_eq_gammaPos (sigma : R →+* S)
    (B : DividedPowerChainAlgebra.{uS, uB} S) (n : ℕ+)
    (x : (graded sigma B).evenPositivePart) :
    gamma sigma B n x =
      (graded sigma B).evenPositiveToEven (gammaPos sigma B n x) := sorry

/-- A restricted divided power of a homogeneous positive-even element remains concentrated in
the expected homogeneous degree. -/
theorem gamma_degree (sigma : R →+* S)
    (B : DividedPowerChainAlgebra.{uS, uB} S) (n d : ℕ)
    (x : (graded sigma B).piece (2 * (d + 1))) :
    ∃ y : (graded sigma B).piece (2 * (n * (d + 1))),
      gamma sigma B n ((graded sigma B).evenPositiveHom d x) =
        (graded sigma B).evenHom (n * (d + 1)) y := sorry

/-- The first restricted divided power is the positive-even inclusion. -/
theorem gamma_one (sigma : R →+* S)
    (B : DividedPowerChainAlgebra.{uS, uB} S)
    (x : (graded sigma B).evenPositivePart) :
    gamma sigma B 1 x = (graded sigma B).evenPositiveToEven x := sorry

/-- The zeroth restricted divided power is the graded unit. -/
theorem gamma_zero (sigma : R →+* S)
    (B : DividedPowerChainAlgebra.{uS, uB} S)
    (x : (graded sigma B).evenPositivePart) :
    gamma sigma B 0 x = (graded sigma B).oneEven := sorry

/-- Restricted divided powers satisfy the binomial product formula. -/
theorem gamma_mul (sigma : R →+* S)
    (B : DividedPowerChainAlgebra.{uS, uB} S) (n m : ℕ)
    (x : (graded sigma B).evenPositivePart) :
    (graded sigma B).evenMul (gamma sigma B n x) (gamma sigma B m x) =
      Nat.choose (n + m) n • gamma sigma B (n + m) x := sorry

/-- Restricted divided powers satisfy the even-multiple formula. -/
theorem gamma_evenMul (sigma : R →+* S)
    (B : DividedPowerChainAlgebra.{uS, uB} S) (n : ℕ)
    (x : (graded sigma B).evenPart) (y : (graded sigma B).evenPositivePart) :
    gamma sigma B n ((graded sigma B).evenMulPositive x y) =
      (graded sigma B).evenMul ((graded sigma B).evenPow x n)
        (gamma sigma B n y) := sorry

/-- Higher restricted divided powers of a product of homogeneous odd elements vanish. -/
theorem gamma_oddMul (sigma : R →+* S)
    (B : DividedPowerChainAlgebra.{uS, uB} S) {n : ℕ} (hn : 1 < n)
    (i j : ℕ) (x : (graded sigma B).piece (2 * i + 1))
    (y : (graded sigma B).piece (2 * j + 1)) :
    gamma sigma B n ((graded sigma B).oddMulTerm i j x y) = 0 := sorry

/-- Restricted divided powers turn addition into the antidiagonal convolution. -/
theorem gamma_add (sigma : R →+* S)
    (B : DividedPowerChainAlgebra.{uS, uB} S) (n : ℕ)
    (x y : (graded sigma B).evenPositivePart) :
    gamma sigma B n (x + y) =
      (Finset.antidiagonal n).sum fun ij ↦
        (graded sigma B).evenMul (gamma sigma B ij.1 x) (gamma sigma B ij.2 y) := sorry

/-- Iterated restricted divided powers use the canonical composition coefficient. -/
theorem gamma_comp (sigma : R →+* S)
    (B : DividedPowerChainAlgebra.{uS, uB} S) (n : ℕ) (m : ℕ+)
    (x : (graded sigma B).evenPositivePart) :
    gamma sigma B n (gammaPos sigma B m x) =
      Nat.uniformBell n m • gamma sigma B (n * (m : ℕ)) x := sorry

/-- The divided-power structure on the restricted nonnegative graded algebra.  Both operation
families retain their original functions; only their scalar-linear ambient structures change. -/
@[stacks 09PQ "divided powers under restriction of scalars"]
def dividedPowers (sigma : R →+* S)
    (B : DividedPowerChainAlgebra.{uS, uB} S) :
    NonnegGradedAlgebra.DividedPowers (graded sigma B) where
  gamma := gamma sigma B
  gammaPos := gammaPos sigma B
  gamma_eq_gammaPos := gamma_eq_gammaPos sigma B
  gamma_degree := gamma_degree sigma B
  gamma_one := gamma_one sigma B
  gamma_zero := gamma_zero sigma B
  gamma_mul := gamma_mul sigma B
  gamma_evenMul := gamma_evenMul sigma B
  gamma_oddMul := gamma_oddMul sigma B
  gamma_add := gamma_add sigma B
  gamma_comp := gamma_comp sigma B

/-- The restricted divided-power operations remain compatible with the unchanged chain
differential. -/
theorem compatible (sigma : R →+* S)
    (B : DividedPowerChainAlgebra.{uS, uB} S) :
    ChainDGAlgebra.DividedPowers.IsCompatible
      (B.toChainDGAlgebra.restrictScalars sigma)
      (dividedPowers sigma B) := sorry

end RestrictScalars

/-- Restrict a divided-power chain DGA along a homomorphism of commutative scalar rings. -/
@[stacks 09PQ "restriction of scalars for divided-power chain differential graded algebras"]
def restrictScalars (sigma : R →+* S)
    (B : DividedPowerChainAlgebra.{uS, uB} S) :
    DividedPowerChainAlgebra.{uR, uB} R where
  toChainDGAlgebra := B.toChainDGAlgebra.restrictScalars sigma
  isStrictlyCommutative := inferInstance
  isNonnegative := inferInstance
  gamma := RestrictScalars.dividedPowers sigma B
  compatible := RestrictScalars.compatible sigma B

/-- The chain DGA underlying a restricted divided-power chain DGA is the generic restricted
chain DGA. -/
@[simp]
theorem restrictScalars_toChainDGAlgebra (sigma : R →+* S)
    (B : DividedPowerChainAlgebra.{uS, uB} S) :
    (restrictScalars sigma B).toChainDGAlgebra =
      B.toChainDGAlgebra.restrictScalars sigma := sorry

/-- A homogeneous component of a restricted divided-power chain DGA is the corresponding
restricted module. -/
@[simp]
theorem restrictScalars_X (sigma : R →+* S)
    (B : DividedPowerChainAlgebra.{uS, uB} S) (n : ℤ) :
    (restrictScalars sigma B).toChainDGAlgebra.X n =
      B.toChainDGAlgebra.restrictScalarsPiece sigma n := sorry

/-- The differential of a restricted divided-power chain DGA is the original differential on
elements. -/
@[simp]
theorem restrictScalars_d (sigma : R →+* S)
    (B : DividedPowerChainAlgebra.{uS, uB} S) (n : ℤ)
    (x : (restrictScalars sigma B).toChainDGAlgebra.X n) :
    (restrictScalars sigma B).toChainDGAlgebra.d n x =
      B.toChainDGAlgebra.d n x := sorry

/-- Multiplication in a restricted divided-power chain DGA is the original homogeneous
multiplication. -/
@[simp]
theorem restrictScalars_mul (sigma : R →+* S)
    (B : DividedPowerChainAlgebra.{uS, uB} S) (n m : ℤ)
    (x : (restrictScalars sigma B).toChainDGAlgebra.X n)
    (y : (restrictScalars sigma B).toChainDGAlgebra.X m) :
    (restrictScalars sigma B).toChainDGAlgebra.mul n m x y =
      B.toChainDGAlgebra.mul n m x y := sorry

/-- The unit of a restricted divided-power chain DGA is the original unit. -/
@[simp]
theorem restrictScalars_one (sigma : R →+* S)
    (B : DividedPowerChainAlgebra.{uS, uB} S) :
    (restrictScalars sigma B).toChainDGAlgebra.one =
      B.toChainDGAlgebra.one := sorry

/-- The total divided-power operation of a restricted object is the original operation on
elements. -/
@[simp]
theorem restrictScalars_gamma (sigma : R →+* S)
    (B : DividedPowerChainAlgebra.{uS, uB} S) (n : ℕ)
    (x : (restrictScalars sigma B).toChainDGAlgebra.nonnegativePart.evenPositivePart) :
    (restrictScalars sigma B).gamma n x = B.gamma n x := sorry

/-- The positive restricted divided-power operation is the original positive operation on
elements. -/
@[simp]
theorem restrictScalars_gammaPos (sigma : R →+* S)
    (B : DividedPowerChainAlgebra.{uS, uB} S) (n : ℕ+)
    (x : (restrictScalars sigma B).toChainDGAlgebra.nonnegativePart.evenPositivePart) :
    (restrictScalars sigma B).gamma.gammaPos n x = B.gamma.gammaPos n x := sorry

/-- Homogeneous divided-power values are unchanged by restriction of scalars. -/
@[simp]
theorem restrictScalars_gammaPiece (sigma : R →+* S)
    (B : DividedPowerChainAlgebra.{uS, uB} S) (n d : ℕ)
    (x : (restrictScalars sigma B).toChainDGAlgebra.nonnegativePart.piece
      (2 * (d + 1))) :
    (restrictScalars sigma B).gamma.gammaPiece n d x =
      B.gamma.gammaPiece n d x := sorry

namespace Hom

variable {B C : DividedPowerChainAlgebra.{uS, uB} S}

/-- The chain map obtained by applying module restriction degreewise to a divided-power
chain-DGA homomorphism. -/
def restrictScalarsChainMap (sigma : R →+* S) (f : Hom B C) :
    (B.toChainDGAlgebra.restrictScalars sigma).toChainComplex ⟶
      (C.toChainDGAlgebra.restrictScalars sigma).toChainComplex :=
  ((ModuleCat.restrictScalars sigma).mapHomologicalComplex (ComplexShape.down ℤ)).map
    f.toChainHom.toChainMap

/-- The restricted chain map acts degreewise by the original homomorphism. -/
@[simp]
theorem restrictScalarsChainMap_apply (sigma : R →+* S) (f : Hom B C)
    (n : ℤ) (x : (B.toChainDGAlgebra.restrictScalars sigma).X n) :
    (f.restrictScalarsChainMap sigma).f n x = f n x := sorry

/-- The restricted chain map preserves the homogeneous unit. -/
theorem restrictScalarsChainMap_one (sigma : R →+* S) (f : Hom B C) :
    (f.restrictScalarsChainMap sigma).f 0
        (B.toChainDGAlgebra.restrictScalars sigma).one =
      (C.toChainDGAlgebra.restrictScalars sigma).one := sorry

/-- The restricted chain map preserves homogeneous multiplication. -/
theorem restrictScalarsChainMap_mul (sigma : R →+* S) (f : Hom B C)
    (n m : ℤ) (x : (B.toChainDGAlgebra.restrictScalars sigma).X n)
    (y : (B.toChainDGAlgebra.restrictScalars sigma).X m) :
    (f.restrictScalarsChainMap sigma).f (n + m)
        ((B.toChainDGAlgebra.restrictScalars sigma).mul n m x y) =
      (C.toChainDGAlgebra.restrictScalars sigma).mul n m
        ((f.restrictScalarsChainMap sigma).f n x)
        ((f.restrictScalarsChainMap sigma).f m y) := sorry

/-- The chain-DGA homomorphism obtained by restricting the scalars of both source and target. -/
def restrictScalarsChainHom (sigma : R →+* S) (f : Hom B C) :
    ChainDGAlgebra.Hom (B.toChainDGAlgebra.restrictScalars sigma)
      (C.toChainDGAlgebra.restrictScalars sigma) where
  toChainMap := f.restrictScalarsChainMap sigma
  map_one := f.restrictScalarsChainMap_one sigma
  map_mul := f.restrictScalarsChainMap_mul sigma

/-- Restricting both scalar structures of a divided-power map preserves its total
divided-power compatibility. -/
theorem restrictScalars_map_gamma (sigma : R →+* S) (f : Hom B C) (n : ℕ)
    (x : (restrictScalars sigma B).toChainDGAlgebra.nonnegativePart.evenPositivePart) :
    (f.restrictScalarsChainHom sigma).nonnegativePart.evenMap
        ((restrictScalars sigma B).gamma n x) =
      (restrictScalars sigma C).gamma n
        ((f.restrictScalarsChainHom sigma).nonnegativePart.evenPositiveMap x) := sorry

/-- Restrict the scalars of a divided-power chain-DGA homomorphism on both its source and
target. -/
@[stacks 09PQ "restriction of scalars on divided-power chain-DGA morphisms"]
def restrictScalars (sigma : R →+* S) (f : Hom B C) :
    Hom (DividedPowerChainAlgebra.restrictScalars sigma B)
      (DividedPowerChainAlgebra.restrictScalars sigma C) where
  toChainHom := f.restrictScalarsChainHom sigma
  map_gamma := f.restrictScalars_map_gamma sigma

/-- Restricting scalars does not change the pointwise action of a divided-power homomorphism. -/
@[simp]
theorem restrictScalars_apply (sigma : R →+* S) (f : Hom B C) (n : ℤ)
    (x : (DividedPowerChainAlgebra.restrictScalars sigma B).toChainDGAlgebra.X n) :
    f.restrictScalars sigma n x = f n x := sorry

/-- Restriction of scalars preserves identity divided-power homomorphisms. -/
@[simp]
theorem restrictScalars_id (sigma : R →+* S)
    (B : DividedPowerChainAlgebra.{uS, uB} S) :
    restrictScalars sigma (𝟙 B) =
      𝟙 (DividedPowerChainAlgebra.restrictScalars sigma B) := sorry

/-- Restriction of scalars preserves composition of divided-power homomorphisms. -/
@[simp]
theorem restrictScalars_comp (sigma : R →+* S)
    {B C D : DividedPowerChainAlgebra.{uS, uB} S} (f : B ⟶ C) (g : C ⟶ D) :
    restrictScalars sigma (Hom.comp g f) =
      Hom.comp (restrictScalars sigma g) (restrictScalars sigma f) := sorry

end Hom

/-- Restriction of scalars is functorial on divided-power chain DGAs with a fixed carrier
universe. -/
@[stacks 09PQ "restriction-of-scalars functor for divided-power chain DGAs"]
def restrictScalarsFunctor (sigma : R →+* S) :
    DividedPowerChainAlgebra.{uS, uB} S ⥤
      DividedPowerChainAlgebra.{uR, uB} R where
  obj B := restrictScalars sigma B
  map f := Hom.restrictScalars sigma f
  map_id := Hom.restrictScalars_id sigma
  map_comp := Hom.restrictScalars_comp sigma

namespace SemilinearHom

variable {sigma : R →+* S}
variable {A : DividedPowerChainAlgebra.{uR, uB} R}
variable {B : DividedPowerChainAlgebra.{uS, uB} S}

/-!
The equivalence below has one common carrier universe because the existing ordinary
`DividedPowerChainAlgebra.Hom` is a morphism in a fixed `ModuleCat` universe.  The semilinear
owner itself remains polymorphic in the source and target carrier universes.
-/

/-- The generic restricted-target chain-DGA map underlying a semilinear divided-power map
preserves the restricted divided powers. -/
theorem toRestrictScalarsHom_map_gamma (f : SemilinearHom sigma A B) (n : ℕ)
    (x : A.toChainDGAlgebra.nonnegativePart.evenPositivePart) :
    f.toChainHom.toRestrictScalarsHom.nonnegativePart.evenMap (A.gamma n x) =
      (DividedPowerChainAlgebra.restrictScalars sigma B).gamma n
        (f.toChainHom.toRestrictScalarsHom.nonnegativePart.evenPositiveMap x) := sorry

/-- Regard a semilinear divided-power chain-DGA map as an ordinary map into the scalar
restriction of its target. -/
@[stacks 09PQ "semilinear divided-power map as a restricted-target map"]
def toRestrictScalarsHom (f : SemilinearHom sigma A B) :
    Hom A (DividedPowerChainAlgebra.restrictScalars sigma B) where
  toChainHom := f.toChainHom.toRestrictScalarsHom
  map_gamma := f.toRestrictScalarsHom_map_gamma

/-- Passing to a restricted target does not change the pointwise action of a semilinear
divided-power map. -/
@[simp]
theorem toRestrictScalarsHom_apply (f : SemilinearHom sigma A B) (n : ℤ)
    (x : A.toChainDGAlgebra.X n) :
    f.toRestrictScalarsHom n x = f n x := sorry

/-- The generic semilinear chain-DGA map recovered from a restricted-target divided-power map
preserves the original divided powers. -/
theorem ofRestrictScalarsHom_map_gamma
    (f : Hom A (DividedPowerChainAlgebra.restrictScalars sigma B)) (n : ℕ)
    (x : A.toChainDGAlgebra.nonnegativePart.evenPositivePart) :
    Semilinear.evenMap
        (ChainDGAlgebra.SemilinearHom.ofRestrictScalarsHom f.toChainHom)
        (A.gamma n x) =
      B.gamma n
        (Semilinear.evenPositiveMap
          (ChainDGAlgebra.SemilinearHom.ofRestrictScalarsHom f.toChainHom) x) := sorry

/-- Regard an ordinary divided-power map into a restricted target as a semilinear map into the
original target. -/
def ofRestrictScalarsHom
    (f : Hom A (DividedPowerChainAlgebra.restrictScalars sigma B)) :
    SemilinearHom sigma A B where
  toChainHom := ChainDGAlgebra.SemilinearHom.ofRestrictScalarsHom f.toChainHom
  map_gamma := ofRestrictScalarsHom_map_gamma f

/-- Recovering a semilinear divided-power map preserves the pointwise action of the
restricted-target map. -/
@[simp]
theorem ofRestrictScalarsHom_apply
    (f : Hom A (DividedPowerChainAlgebra.restrictScalars sigma B)) (n : ℤ)
    (x : A.toChainDGAlgebra.X n) :
    ofRestrictScalarsHom f n x = f n x := sorry

/-- Converting a semilinear divided-power map to a restricted-target map and back is the
identity. -/
@[simp]
theorem ofRestrictScalarsHom_toRestrictScalarsHom (f : SemilinearHom sigma A B) :
    ofRestrictScalarsHom f.toRestrictScalarsHom = f := sorry

/-- Converting a restricted-target divided-power map to a semilinear map and back is the
identity. -/
@[simp]
theorem toRestrictScalarsHom_ofRestrictScalarsHom
    (f : Hom A (DividedPowerChainAlgebra.restrictScalars sigma B)) :
    (ofRestrictScalarsHom f).toRestrictScalarsHom = f := sorry

/-- Semilinear divided-power chain-DGA maps are canonically equivalent to ordinary maps into
the restriction of scalars of the target. -/
@[stacks 09PQ "semilinear and restricted-scalar divided-power chain-DGA morphisms"]
def restrictScalarsHomEquiv :
    SemilinearHom sigma A B ≃
      Hom A (DividedPowerChainAlgebra.restrictScalars sigma B) where
  toFun := toRestrictScalarsHom
  invFun := ofRestrictScalarsHom
  left_inv := ofRestrictScalarsHom_toRestrictScalarsHom
  right_inv := toRestrictScalarsHom_ofRestrictScalarsHom

/-- The restricted-scalar Hom equivalence acts pointwise as the original semilinear map. -/
@[simp]
theorem restrictScalarsHomEquiv_apply (f : SemilinearHom sigma A B) (n : ℤ)
    (x : A.toChainDGAlgebra.X n) :
    restrictScalarsHomEquiv f n x = f n x := sorry

/-- The inverse restricted-scalar Hom equivalence acts pointwise as the ordinary map into the
restricted target. -/
@[simp]
theorem restrictScalarsHomEquiv_symm_apply
    (f : Hom A (DividedPowerChainAlgebra.restrictScalars sigma B)) (n : ℤ)
    (x : A.toChainDGAlgebra.X n) :
    restrictScalarsHomEquiv.symm f n x = f n x := sorry

end SemilinearHom

end DividedPowerChainAlgebra
