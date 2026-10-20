/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.LinearAlgebra.StdBasis
public import ReasLib.RingTheory.DividedPowers.Tate
public import ReasLib.RingTheory.Ideal.FiniteGeneration.PowerFamily
public import ReasLib.RingTheory.Sequence.Koszul.ChainDGA
import Mathlib.Tactic.CrossRefAttribute

/-!
# Powered Koszul--Tate approximations

This file gives the powered Koszul exterior DGA its reusable divided-power interface. Exact
exponents own the mathematical stages and transitions; the zero-based sequential functor has
stage `j` equal to exact exponent `j + 1`. The canonical augmentation identifies zeroth Koszul
homology with the corresponding finite-power quotient.

The approximation owner specializes a Tate resolution with no degree-zero variables. It retains
the two Koszul comparison maps, the canonical augmentation triangle, the transition triangle, and
the induced map between finite-power quotients on zeroth homology. Its existence is theorem data:
no public definition chooses an approximation from that existence statement.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite

universe u x

variable {R : Type u} [CommRing R]

namespace KoszulComplex.ChainDGA

/-- The canonical identification of degree zero in an exact-power Koszul chain DGA with the base
ring. -/
@[stacks 0GZ4 "degree zero of an exact-power Koszul DGA"]
def powDegreeZeroIso {ι : Type u} [Finite ι] (f : ι → R) (n : ℕ) :
    (pow f n).X 0 ≅ ModuleCat.of R R :=
  (KoszulComplex.powComplex f n).extendXIso ChainDGAlgebra.natEmbedding rfl ≪≫
    ModuleCat.exteriorPower.iso₀ (ModuleCat.of R (ι → R))

/-- The degree-zero map from an exact-power Koszul DGA to its canonical finite-power quotient. -/
@[stacks 0GZ4 "degree-zero powered Koszul quotient map"]
def powDegreeZeroQuotientMap {ι : Type u} [Finite ι] (f : ι → R) (n : ℕ) :
    (pow f n).X 0 ⟶ ModuleCat.of R (R ⧸ Ideal.powerSpan f n) :=
  (powDegreeZeroIso f n).hom ≫
    ModuleCat.ofHom (Ideal.Quotient.mkₐ R (Ideal.powerSpan f n)).toLinearMap

/-- The degree-zero quotient map sends a Koszul scalar to its residue class. -/
@[simp, stacks 0GZ4 "evaluation of the degree-zero powered Koszul quotient map"]
theorem powDegreeZeroQuotientMap_apply {ι : Type u} [Finite ι] (f : ι → R) (n : ℕ)
    (x : (pow f n).X 0) :
    powDegreeZeroQuotientMap f n x =
      Ideal.Quotient.mk (Ideal.powerSpan f n) ((powDegreeZeroIso f n).hom x) := sorry

/-- The exact-power Koszul differential entering degree zero is killed by the canonical quotient
map. -/
@[stacks 0GZ4 "the Koszul differential is killed by the power quotient"]
theorem powDegreeZeroQuotientMap_d {ι : Type u} [Finite ι] (f : ι → R) (n : ℕ)
    (i : ℤ) (hi : (ComplexShape.down ℤ).Rel i 0) :
    (pow f n).toChainComplex.d i 0 ≫ powDegreeZeroQuotientMap f n = 0 := sorry

/-- The canonical chain map from an exact-power Koszul DGA to its quotient in degree zero. -/
@[stacks 0GZ4 "exact-power Koszul augmentation chain map"]
def powAugmentationChainMap {ι : Type u} [Finite ι] (f : ι → R) (n : ℕ) :
    (pow f n).toChainComplex ⟶
      ChainDGAlgebra.degreeZeroComplex R (R ⧸ Ideal.powerSpan f n) :=
  HomologicalComplex.mkHomToSingle (powDegreeZeroQuotientMap f n)
    (powDegreeZeroQuotientMap_d f n)

/-- The degree-zero component of the canonical Koszul augmentation is the finite-power quotient
map. -/
@[simp, stacks 0GZ4 "degree-zero component of the exact-power augmentation"]
theorem powAugmentationChainMap_f_zero {ι : Type u} [Finite ι] (f : ι → R) (n : ℕ) :
    (powAugmentationChainMap f n).f 0 =
      powDegreeZeroQuotientMap f n ≫
        (ChainDGAlgebra.degreeZeroIso R (R ⧸ Ideal.powerSpan f n)).inv := sorry

/-- The canonical Koszul augmentation preserves the homogeneous unit. -/
@[stacks 0GZ4 "unit law for the exact-power Koszul augmentation"]
theorem powAugmentation_map_one {ι : Type u} [Finite ι] (f : ι → R) (n : ℕ) :
    (ChainDGAlgebra.degreeZeroIso R (R ⧸ Ideal.powerSpan f n)).hom
        ((powAugmentationChainMap f n).f 0 (pow f n).one) = 1 := sorry

/-- The canonical Koszul augmentation preserves multiplication in degree zero. -/
@[stacks 0GZ4 "multiplication law for the exact-power Koszul augmentation"]
theorem powAugmentation_map_mul {ι : Type u} [Finite ι] (f : ι → R) (n : ℕ)
    (x y : (pow f n).X 0) :
    (ChainDGAlgebra.degreeZeroIso R (R ⧸ Ideal.powerSpan f n)).hom
        ((powAugmentationChainMap f n).f 0 ((pow f n).mul 0 0 x y)) =
      (ChainDGAlgebra.degreeZeroIso R (R ⧸ Ideal.powerSpan f n)).hom
          ((powAugmentationChainMap f n).f 0 x) *
        (ChainDGAlgebra.degreeZeroIso R (R ⧸ Ideal.powerSpan f n)).hom
          ((powAugmentationChainMap f n).f 0 y) := sorry

/-- The canonical augmentation of an exact-power Koszul DGA to the quotient by the same powers. -/
@[stacks 0GZ4 "canonical exact-power Koszul augmentation"]
def augmentation {ι : Type u} [Finite ι] (f : ι → R) (n : ℕ) :
    ChainDGAlgebra.Augmentation (pow f n) (R ⧸ Ideal.powerSpan f n) where
  toChainMap := powAugmentationChainMap f n
  map_one := powAugmentation_map_one f n
  map_mul := powAugmentation_map_mul f n

/-- The chain map underlying the canonical Koszul augmentation is the explicit single-term map. -/
@[simp, stacks 0GZ4 "underlying map of the exact-power Koszul augmentation"]
theorem augmentation_toChainMap {ι : Type u} [Finite ι] (f : ι → R) (n : ℕ) :
    (augmentation f n).toChainMap = powAugmentationChainMap f n := sorry

/-- The canonical augmentation map on zeroth Koszul homology is a bijection onto the
finite-power quotient. -/
@[stacks 0GZ4 "zeroth homology of an exact-power Koszul DGA"]
theorem homologyZeroMap_bijective {ι : Type u} [Finite ι] (f : ι → R) (n : ℕ) :
    Function.Bijective (augmentation f n).homologyZeroMap := sorry

end KoszulComplex.ChainDGA

namespace KoszulComplex.PowerQuotient

/-- The canonical polynomial presentation with no variables of a quotient by a family of fixed
powers. -/
@[stacks 0GZ4 "constant polynomial presentation of a power-family quotient"]
def presentation {ι : Type u} (f : ι → R) (n : ℕ) :
    MvPolynomial Empty R →ₐ[R] R ⧸ Ideal.powerSpan f n :=
  (Ideal.Quotient.mkₐ R (Ideal.powerSpan f n)).comp
    (MvPolynomial.isEmptyAlgEquiv R Empty).toAlgHom

/-- The constant polynomial presentation of a quotient by a family of fixed powers is
surjective. -/
@[stacks 0GZ4 "surjectivity of the power-family quotient presentation"]
theorem presentation_surjective {ι : Type u} (f : ι → R) (n : ℕ) :
    Function.Surjective (presentation f n) := sorry

end KoszulComplex.PowerQuotient

namespace KoszulComplex.DP

/-- Compatible divided powers on every exact-power Koszul DGA. The underlying DGAs and maps are
the canonical `KoszulComplex.ChainDGA.pow` and `KoszulComplex.ChainDGA.powMap`; only the divided
power operations and their proposition-valued compatibility laws are additional fields. -/
@[stacks 0GZ4 "divided powers on the powered Koszul system"]
structure System {ι : Type u} [Finite ι] (f : ι → R) where
  /-- Divided powers on the positive even part of exact-power stage `n`. -/
  gamma (n : ℕ) :
    NonnegGradedAlgebra.DividedPowers (ChainDGA.pow f n).nonnegativePart
  /-- The divided powers at each exact-power stage are compatible with the differential. -/
  compatible (n : ℕ) :
    ChainDGAlgebra.DividedPowers.IsCompatible (ChainDGA.pow f n) (gamma n)
  /-- Every exact-power Koszul transition preserves divided powers. -/
  map_gamma {n m : ℕ} (h : n ≤ m) (q : ℕ)
      (x : (ChainDGA.pow f m).nonnegativePart.evenPositivePart) :
    (ChainDGA.powMap f h).nonnegativePart.evenMap (gamma m q x) =
      gamma n q ((ChainDGA.powMap f h).nonnegativePart.evenPositiveMap x)

namespace Canonical

variable {ι : Type u} [Finite ι]

namespace Internal

/-- The linearly ordered coordinate model required internally by mathlib's exterior-power basis. -/
abbrev OrderedCoordinateIndex (ι : Type u) [Finite ι] :=
  Fin (Nat.card ι)

/-- The ordered basis used internally to define the exterior-monomial formula. -/
noncomputable def orderedCoordinateBasis :
    Module.Basis (OrderedCoordinateIndex ι) R (ι → R) :=
  (Pi.basisFun R ι).reindex (Finite.equivFin ι)

/-- Indices for the standard exterior-monomial basis of the positive even part of a Koszul
algebra.  An index records a positive even degree and a subset of the finite-ordinal
coordinates of the degree-one generators. -/
abbrev BasisIndex (ι : Type u) [Finite ι] :=
  Σ d : ℕ, Set.powersetCard (OrderedCoordinateIndex ι) (2 * (d + 1))

end Internal

/-- The degree-`k` piece of a powered Koszul chain DGA is canonically the `k`th exterior power of
the free module on its finite family of generators. -/
def pieceEquiv (f : ι → R) (n k : ℕ) :
    (ChainDGA.pow f n).nonnegativePiece k ≃ₗ[R]
      (ModuleCat.of R (ι → R)).exteriorPower k :=
  ((KoszulComplex.powComplex f n).extendXIso ChainDGAlgebra.natEmbedding rfl).toLinearEquiv

namespace Internal

/-- The standard exterior-monomial basis used internally for the divided-power formula. -/
noncomputable def basis (f : ι → R) (n : ℕ) :
    Module.Basis (BasisIndex ι) R
      (ChainDGA.pow f n).nonnegativePart.evenPositivePart :=
  DFinsupp.basis fun d ↦
    ((orderedCoordinateBasis (R := R) (ι := ι)).exteriorPower (2 * (d + 1))).map
      (pieceEquiv f n (2 * (d + 1))).symm

end Internal

/-- Multiplication on the even part of a powered Koszul algebra is commutative. -/
theorem evenMul_comm (f : ι → R) (n : ℕ)
    (x y : (ChainDGA.pow f n).nonnegativePart.evenPart) :
    (ChainDGA.pow f n).nonnegativePart.evenMul x y =
      (ChainDGA.pow f n).nonnegativePart.evenMul y x := sorry

/-- Multiplication on the even part of a powered Koszul algebra is associative. -/
theorem evenMul_assoc (f : ι → R) (n : ℕ)
    (x y z : (ChainDGA.pow f n).nonnegativePart.evenPart) :
    (ChainDGA.pow f n).nonnegativePart.evenMul
        ((ChainDGA.pow f n).nonnegativePart.evenMul x y) z =
      (ChainDGA.pow f n).nonnegativePart.evenMul x
        ((ChainDGA.pow f n).nonnegativePart.evenMul y z) := sorry

/-- The canonical commutativity instance used to fold finite products in the even part. -/
instance instEvenMulCommutative (f : ι → R) (n : ℕ) :
    Std.Commutative
      (fun x y ↦ (ChainDGA.pow f n).nonnegativePart.evenMul x y) :=
  ⟨evenMul_comm f n⟩

/-- The canonical associativity instance used to fold finite products in the even part. -/
instance instEvenMulAssociative (f : ι → R) (n : ℕ) :
    Std.Associative
      (fun x y ↦ (ChainDGA.pow f n).nonnegativePart.evenMul x y) :=
  ⟨evenMul_assoc f n⟩

namespace Internal

/-- The scalar-weighted exterior monomial contributed by one internal basis coordinate. -/
def basisFactor (f : ι → R) (n : ℕ)
    (x : (ChainDGA.pow f n).nonnegativePart.evenPositivePart) (i : BasisIndex ι) :
    (ChainDGA.pow f n).nonnegativePart.evenPart :=
  (ChainDGA.pow f n).nonnegativePart.evenPositiveToEven
    (((basis f n).repr x i : R) • basis f n i)

/-- The product of scalar-weighted internal basis monomials indexed by a finite subset. -/
def basisProduct (f : ι → R) (n : ℕ)
    (x : (ChainDGA.pow f n).nonnegativePart.evenPositivePart)
    (s : Finset (BasisIndex ι)) : (ChainDGA.pow f n).nonnegativePart.evenPart :=
  s.fold (fun a b ↦ (ChainDGA.pow f n).nonnegativePart.evenMul a b)
    (ChainDGA.pow f n).nonnegativePart.oneEven (basisFactor f n x)

end Internal

/-- The canonical divided-power formula on a powered Koszul exterior algebra: `gamma q x` is the
sum of the products indexed by the `q`-element subsets of the support of the standard-basis
expansion of `x`. -/
@[stacks 0GZ4 "canonical divided-power formula on a powered Koszul stage"]
def gamma (f : ι → R) (n q : ℕ)
    (x : (ChainDGA.pow f n).nonnegativePart.evenPositivePart) :
    (ChainDGA.pow f n).nonnegativePart.evenPart :=
  (((Internal.basis f n).repr x).support.powersetCard q).sum
    (Internal.basisProduct f n x)

/-- Every positive-index canonical divided power is projected to its positive-even homogeneous
summands. -/
@[stacks 0GZ4 "positive canonical divided-power formula on a powered Koszul stage"]
def gammaPos (f : ι → R) (n : ℕ) (q : ℕ+)
    (x : (ChainDGA.pow f n).nonnegativePart.evenPositivePart) :
    (ChainDGA.pow f n).nonnegativePart.evenPositivePart :=
  (ChainDGA.pow f n).nonnegativePart.evenToEvenPositive (gamma f n q x)

/-- The positive-index refinement of the canonical formula agrees with the total operation. -/
theorem gamma_eq_gammaPos (f : ι → R) (n : ℕ) (q : ℕ+)
    (x : (ChainDGA.pow f n).nonnegativePart.evenPositivePart) :
    gamma f n q x =
      (ChainDGA.pow f n).nonnegativePart.evenPositiveToEven (gammaPos f n q x) := sorry

/-- The canonical divided power of a homogeneous element has the expected multiplied degree. -/
theorem gamma_degree (f : ι → R) (n q d : ℕ)
    (x : (ChainDGA.pow f n).nonnegativePart.piece (2 * (d + 1))) :
    ∃ y : (ChainDGA.pow f n).nonnegativePart.piece (2 * (q * (d + 1))),
      gamma f n q ((ChainDGA.pow f n).nonnegativePart.evenPositiveHom d x) =
        (ChainDGA.pow f n).nonnegativePart.evenHom (q * (d + 1)) y := sorry

/-- The first canonical divided power is the positive-even inclusion. -/
theorem gamma_one (f : ι → R) (n : ℕ)
    (x : (ChainDGA.pow f n).nonnegativePart.evenPositivePart) :
    gamma f n 1 x = (ChainDGA.pow f n).nonnegativePart.evenPositiveToEven x := sorry

/-- The zeroth canonical divided power is the graded unit. -/
theorem gamma_zero (f : ι → R) (n : ℕ)
    (x : (ChainDGA.pow f n).nonnegativePart.evenPositivePart) :
    gamma f n 0 x = (ChainDGA.pow f n).nonnegativePart.oneEven := sorry

/-- Products of canonical divided powers satisfy the binomial identity. -/
theorem gamma_mul (f : ι → R) (stage q p : ℕ)
    (x : (ChainDGA.pow f stage).nonnegativePart.evenPositivePart) :
    (ChainDGA.pow f stage).nonnegativePart.evenMul (gamma f stage q x)
        (gamma f stage p x) =
      Nat.choose (q + p) q • gamma f stage (q + p) x := sorry

/-- Canonical divided powers respect multiplication by an even element. -/
theorem gamma_evenMul (f : ι → R) (stage q : ℕ)
    (x : (ChainDGA.pow f stage).nonnegativePart.evenPart)
    (y : (ChainDGA.pow f stage).nonnegativePart.evenPositivePart) :
    gamma f stage q ((ChainDGA.pow f stage).nonnegativePart.evenMulPositive x y) =
      (ChainDGA.pow f stage).nonnegativePart.evenMul
        ((ChainDGA.pow f stage).nonnegativePart.evenPow x q) (gamma f stage q y) := sorry

/-- Higher canonical divided powers vanish on a product of homogeneous odd elements. -/
theorem gamma_oddMul (f : ι → R) (stage : ℕ) {q : ℕ} (hq : 1 < q)
    (i j : ℕ) (x : (ChainDGA.pow f stage).nonnegativePart.piece (2 * i + 1))
    (y : (ChainDGA.pow f stage).nonnegativePart.piece (2 * j + 1)) :
    gamma f stage q ((ChainDGA.pow f stage).nonnegativePart.oddMulTerm i j x y) = 0 := sorry

/-- Canonical divided powers turn addition into antidiagonal convolution. -/
theorem gamma_add (f : ι → R) (stage q : ℕ)
    (x y : (ChainDGA.pow f stage).nonnegativePart.evenPositivePart) :
    gamma f stage q (x + y) =
      (Finset.antidiagonal q).sum fun ij ↦
        (ChainDGA.pow f stage).nonnegativePart.evenMul
          (gamma f stage ij.1 x) (gamma f stage ij.2 y) := sorry

/-- Iterating canonical divided powers gives the standard uniform-Bell coefficient. -/
theorem gamma_comp (f : ι → R) (stage q : ℕ) (p : ℕ+)
    (x : (ChainDGA.pow f stage).nonnegativePart.evenPositivePart) :
    gamma f stage q (gammaPos f stage p x) =
      Nat.uniformBell q p • gamma f stage (q * (p : ℕ)) x := sorry

/-- The concrete standard-basis formula defines divided powers on a powered Koszul stage. -/
@[stacks 0GZ4 "canonical divided powers on a powered Koszul stage"]
def dividedPowers (f : ι → R) (n : ℕ) :
    NonnegGradedAlgebra.DividedPowers (ChainDGA.pow f n).nonnegativePart where
  gamma := gamma f n
  gammaPos := gammaPos f n
  gamma_eq_gammaPos := gamma_eq_gammaPos f n
  gamma_degree := gamma_degree f n
  gamma_one := gamma_one f n
  gamma_zero := gamma_zero f n
  gamma_mul := gamma_mul f n
  gamma_evenMul := gamma_evenMul f n
  gamma_oddMul := gamma_oddMul f n
  gamma_add := gamma_add f n
  gamma_comp := gamma_comp f n

/-- Evaluation of the canonical divided-power structure is the standard exterior-basis formula. -/
@[simp, stacks 0GZ4 "evaluation of canonical powered Koszul divided powers"]
theorem dividedPowers_apply (f : ι → R) (n q : ℕ)
    (x : (ChainDGA.pow f n).nonnegativePart.evenPositivePart) :
    dividedPowers f n q x = gamma f n q x := sorry

/-- The canonical divided powers on a powered Koszul stage are compatible with its differential. -/
@[stacks 0GZ4 "differential compatibility of canonical powered Koszul divided powers"]
theorem isCompatible (f : ι → R) (n : ℕ) :
    ChainDGAlgebra.DividedPowers.IsCompatible
      (ChainDGA.pow f n) (dividedPowers f n) := sorry

/-- Every exact-power Koszul transition preserves the canonical divided-power formula. -/
@[stacks 0GZ4 "naturality of canonical powered Koszul divided powers"]
theorem map_gamma (f : ι → R) {n m : ℕ} (h : n ≤ m) (q : ℕ)
    (x : (ChainDGA.pow f m).nonnegativePart.evenPositivePart) :
    (ChainDGA.powMap f h).nonnegativePart.evenMap (dividedPowers f m q x) =
      dividedPowers f n q
        ((ChainDGA.powMap f h).nonnegativePart.evenPositiveMap x) := sorry

namespace Reindex

/-- The exterior-basis formula for canonical divided powers is invariant under finite reindexing
of the Koszul generators. -/
@[stacks 0GZ4 "reindexing naturality of canonical Koszul divided powers"]
theorem gamma_naturality {ι κ : Type u} [Finite ι] [Finite κ]
    (f : ι → R) (e : ι ≃ κ) (n q : ℕ)
    (x : (ChainDGA.pow f n).nonnegativePart.evenPositivePart) :
    (ChainDGA.Reindex.powIso f e n).hom.nonnegativePart.evenMap (gamma f n q x) =
      gamma (fun j ↦ f (e.symm j)) n q
        ((ChainDGA.Reindex.powIso f e n).hom.nonnegativePart.evenPositiveMap x) := sorry

/-- The canonical divided-power structure itself is natural under finite reindexing. -/
@[stacks 0GZ4 "naturality of canonical divided-power structures under reindexing"]
theorem dividedPowers_naturality {ι κ : Type u} [Finite ι] [Finite κ]
    (f : ι → R) (e : ι ≃ κ) (n q : ℕ)
    (x : (ChainDGA.pow f n).nonnegativePart.evenPositivePart) :
    (ChainDGA.Reindex.powIso f e n).hom.nonnegativePart.evenMap
        (dividedPowers f n q x) =
      dividedPowers (fun j ↦ f (e.symm j)) n q
        ((ChainDGA.Reindex.powIso f e n).hom.nonnegativePart.evenPositiveMap x) := sorry

end Reindex

end Canonical

/-- The canonical compatible divided-power system on all exact powers of a finite Koszul family.
Its operations are the explicit standard exterior-basis formula in `DP.Canonical.gamma`. -/
@[stacks 0GZ4 "canonical powered Koszul divided-power system",
  stacks 0GZ5 "canonical powered Koszul divided-power inverse system"]
def system {ι : Type u} [Finite ι] (f : ι → R) : System f where
  gamma := Canonical.dividedPowers f
  compatible := Canonical.isCompatible f
  map_gamma := Canonical.map_gamma f

/-- The divided powers stored at exact exponent `n` in the canonical system are the concrete
standard exterior-basis divided powers. -/
@[simp, stacks 0GZ4 "canonical divided powers stored in the powered Koszul system"]
theorem system_gamma {ι : Type u} [Finite ι] (f : ι → R) (n : ℕ) :
    (system f).gamma n = Canonical.dividedPowers f n := sorry

namespace System

variable {ι : Type u} [Finite ι] {f : ι → R}

/-- A divided-power system is canonical when its stagewise operations are the explicit
standard-basis operations owned by `Canonical.dividedPowers`. -/
@[stacks 0GZ4 "canonicality specification for powered Koszul divided powers"]
def IsCanonical (K : System f) : Prop :=
  ∀ n : ℕ, K.gamma n = Canonical.dividedPowers f n

/-- An exact-power Koszul stage equipped with the divided powers supplied by the system. -/
@[stacks 0GZ4 "exact-power divided-power Koszul DGA"]
def stage (K : System f) (n : ℕ) : DividedPowerChainAlgebra R where
  toChainDGAlgebra := ChainDGA.pow f n
  isStrictlyCommutative := inferInstance
  isNonnegative := inferInstance
  gamma := K.gamma n
  compatible := K.compatible n

/-- The chain DGA underlying an exact divided-power Koszul stage is the canonical exact-power
Koszul DGA. -/
@[simp, stacks 0GZ4 "underlying chain DGA of a divided-power Koszul stage"]
theorem stage_toChainDGAlgebra (K : System f) (n : ℕ) :
    (K.stage n).toChainDGAlgebra = ChainDGA.pow f n := sorry

/-- The divided-power homomorphism between two exact-power Koszul stages. -/
@[stacks 0GZ4 "exact-power divided-power Koszul transition"]
def transition (K : System f) {n m : ℕ} (h : n ≤ m) : K.stage m ⟶ K.stage n where
  toChainHom := ChainDGA.powMap f h
  map_gamma := K.map_gamma h

/-- Forgetting divided powers from an exact-power transition gives the canonical Koszul map. -/
@[simp, stacks 0GZ4 "underlying map of a divided-power Koszul transition"]
theorem transition_toChainHom (K : System f) {n m : ℕ} (h : n ≤ m) :
    (K.transition h).toChainHom = ChainDGA.powMap f h := sorry

/-- The exact-power divided-power transition at a fixed exponent is the identity. -/
@[simp, stacks 0GZ5 "reflexive divided-power Koszul transition"]
theorem transition_refl (K : System f) (n : ℕ) :
    K.transition (le_refl n) = 𝟙 (K.stage n) := sorry

/-- Exact-power divided-power Koszul transitions compose according to transitivity. -/
@[simp, stacks 0GZ5 "composition of divided-power Koszul transitions"]
theorem transition_comp (K : System f) {n m l : ℕ}
    (h_nm : n ≤ m) (h_ml : m ≤ l) :
    K.transition h_ml ≫ K.transition h_nm = K.transition (h_nm.trans h_ml) := sorry

/-- Zero-based stage `j` is exact exponent `j + 1`, with its compatible divided powers. -/
@[stacks 0GZ5 "zero-based divided-power Koszul stage"]
abbrev powerStage (K : System f) (j : ℕ) : DividedPowerChainAlgebra R :=
  K.stage (j + 1)

/-- The adjacent zero-based divided-power Koszul transition. -/
@[stacks 0GZ5 "adjacent divided-power Koszul transition"]
def step (K : System f) (j : ℕ) : K.powerStage (j + 1) ⟶ K.powerStage j :=
  K.transition (Nat.le_succ (j + 1))

/-- The zero-based sequential inverse system of powered Koszul divided-power chain DGAs. -/
@[stacks 0GZ5 "powered Koszul divided-power inverse system"]
def system (K : System f) : ℕᵒᵖ ⥤ DividedPowerChainAlgebra R :=
  Functor.ofOpSequence K.step

/-- Object `j` of the zero-based divided-power system is exact exponent `j + 1`. -/
@[simp, stacks 0GZ5 "object of a powered divided-power Koszul system"]
theorem system_obj (K : System f) (j : ℕ) :
    K.system.obj (op j) = K.stage (j + 1) := sorry

/-- An arbitrary zero-based system map is the exact-power transition between exponents increased
by one. -/
@[stacks 0GZ5 "arbitrary powered Koszul divided-power transition"]
theorem system_map (K : System f) {i j : ℕ} (h : i ≤ j) :
    K.system.map (homOfLE h).op =
      K.transition (Nat.add_le_add_right h 1) := sorry

/-- Forgetting divided powers from the zero-based divided-power system recovers the canonical
powered Koszul chain-DGA system. -/
@[stacks 0GZ5 "underlying powered Koszul chain-DGA system"]
theorem system_comp_forget (K : System f) :
    K.system ⋙ DividedPowerChainAlgebra.forget R = ChainDGA.system f := sorry

/-- The canonical divided-power structure on the powered Koszul exterior system exists. -/
@[stacks 0GZ4 "existence of powered Koszul divided powers"]
theorem nonempty (f : ι → R) : Nonempty (System f) := sorry

/-- A powered Koszul divided-power system is determined by its stagewise operations. -/
@[ext]
theorem ext {f : ι → R} (K L : System f)
    (hgamma : ∀ n, K.gamma n = L.gamma n) : K = L := sorry

/-- The explicit system constructor satisfies the canonicality specification. -/
@[stacks 0GZ4 "canonical powered Koszul system satisfies its specification"]
theorem isCanonical_system (f : ι → R) : IsCanonical (KoszulComplex.DP.system f) := sorry

/-- A canonicality witness identifies a supplied divided-power system with the owner `system`. -/
@[stacks 0GZ4 "uniqueness of the canonical powered Koszul system"]
theorem IsCanonical.eq {K : System f} (hK : K.IsCanonical) :
    K = KoszulComplex.DP.system f := sorry

/-- The canonical divided-power system is the unique system satisfying its specification. -/
@[stacks 0GZ4 "unique canonical powered Koszul divided-power system"]
theorem existsUnique_isCanonical (f : ι → R) :
    ∃! K : System f, K.IsCanonical := sorry

end System

/-- The canonical divided-power chain DGA at exact exponent `n`. -/
@[stacks 0GZ4 "canonical exact-power divided-power Koszul DGA"]
abbrev stage {ι : Type u} [Finite ι] (f : ι → R) (n : ℕ) : DividedPowerChainAlgebra R :=
  (system f).stage n

/-- Forgetting divided powers from a canonical exact-power stage gives the powered Koszul chain
DGA at the same exact exponent. -/
@[simp, stacks 0GZ4 "underlying chain DGA of a divided-power Koszul stage"]
theorem stage_toChainDGAlgebra {ι : Type u} [Finite ι] (f : ι → R) (n : ℕ) :
    (stage f n).toChainDGAlgebra = ChainDGA.pow f n := sorry

/-- The divided powers of the canonical exact-power stage are the explicit standard-basis
operations of `Canonical.dividedPowers`. -/
@[simp, stacks 0GZ4 "divided powers of a canonical exact-power Koszul stage"]
theorem stage_gamma {ι : Type u} [Finite ι] (f : ι → R) (n : ℕ) :
    (stage f n).gamma = Canonical.dividedPowers f n := sorry

/-- The canonical divided-power transition from exact exponent `m` to exact exponent `n`. -/
@[stacks 0GZ4 "canonical exact-power divided-power Koszul transition"]
def transition {ι : Type u} [Finite ι] (f : ι → R) {n m : ℕ} (h : n ≤ m) :
    stage f m ⟶ stage f n :=
  (system f).transition h

/-- Forgetting divided powers from a canonical exact-power transition gives the corresponding
powered Koszul chain-DGA map. -/
@[simp, stacks 0GZ4 "underlying map of a divided-power Koszul transition"]
theorem transition_toChainHom {ι : Type u} [Finite ι] (f : ι → R) {n m : ℕ} (h : n ≤ m) :
    (transition f h).toChainHom = ChainDGA.powMap f h := sorry

/-- The canonical zero-based inverse system of powered Koszul divided-power chain DGAs. -/
@[stacks 0GZ5 "canonical powered Koszul divided-power tower"]
def tower {ι : Type u} [Finite ι] (f : ι → R) : ℕᵒᵖ ⥤ DividedPowerChainAlgebra R :=
  (system f).system

/-- Object `j` of the canonical powered Koszul tower is exact exponent `j + 1`. -/
@[simp, stacks 0GZ5 "object of the canonical powered divided-power tower"]
theorem tower_obj {ι : Type u} [Finite ι] (f : ι → R) (j : ℕ) :
    (tower f).obj (op j) = stage f (j + 1) := sorry

/-- An arbitrary map in the canonical zero-based tower is the canonical exact-power transition
between exponents increased by one. -/
@[stacks 0GZ5 "map in the canonical powered divided-power tower"]
theorem tower_map {ι : Type u} [Finite ι] (f : ι → R) {i j : ℕ} (h : i ≤ j) :
    (tower f).map (homOfLE h).op = transition f (Nat.add_le_add_right h 1) := sorry

/-- Forgetting divided powers from the canonical tower gives the canonical powered Koszul
chain-DGA system. -/
@[stacks 0GZ5 "underlying chain-DGA system of the canonical powered Koszul tower"]
theorem tower_comp_forget {ι : Type u} [Finite ι] (f : ι → R) :
    tower f ⋙ DividedPowerChainAlgebra.forget R = ChainDGA.system f := sorry

end KoszulComplex.DP

namespace KoszulComplex.Tate

open KoszulComplex.DP

variable {ι : Type u} [Finite ι] {f : ι → R}

/-- A Tate resolution of the quotient by a fixed exact power, with no degree-zero variables and
positive generator types in the independent universe `x`. -/
@[stacks 0GZ4 "universe-polymorphic positive-generator Tate resolution of a power quotient"]
abbrev Resolution (f : ι → R) (N : ℕ) :=
  TateResolution.Positive.{u, u, x} (PowerQuotient.presentation f N)

namespace FromKoszul

/-- A map from an exact-power Koszul stage into a power-quotient Tate resolution has canonical
augmentation when its augmentation composite is the canonical Koszul augmentation. -/
@[stacks 0GZ4 "canonical augmentation of a Koszul-to-Tate comparison"]
def IsCanonical (K : System f) {N : ℕ} {A : Resolution.{u, x} f N}
    (fromKoszul : K.stage N ⟶ A.algebra) : Prop :=
  A.augmentation.comp fromKoszul.toChainHom = ChainDGA.augmentation f N

end FromKoszul

namespace Comparison

/-- Two comparison maps factor the canonical exact-power Koszul transition. -/
@[stacks 0GZ4 "factorization of a powered Koszul transition"]
def FactorsTransition (K : System f) {n N : ℕ} (h : n ≤ N)
    {A : DividedPowerChainAlgebra R} (fromKoszul : K.stage N ⟶ A)
    (toKoszul : A ⟶ K.stage n) : Prop :=
  fromKoszul ≫ toKoszul = K.transition h

end Comparison

namespace ToKoszul

/-- A map from a power-quotient Tate resolution to an earlier Koszul stage induces the canonical
finite-power quotient transition on zeroth homology. -/
@[stacks 0GZ4 "zeroth-homology compatibility of a Tate-to-Koszul comparison"]
def InducesQuotient (K : System f) {n N : ℕ} (h : n ≤ N)
    {A : Resolution.{u, x} f N} (toKoszul : A.algebra ⟶ K.stage n) : Prop :=
  toKoszul.toChainHom.CommutesOnH0Over (Ideal.powerQuotientMap f h)
    A.augmentation (ChainDGA.augmentation f n)

end ToKoszul

set_option maxHeartbeats 800000 in
/-- Lemma 23.12.1 (Tag 0GZ4): an explicit finite-cell Tate approximation between exact-power
Koszul stages. The exponent `n` is positive and exact, not the zero-based functor index. -/
@[stacks 0GZ4 "powered Koszul--Tate approximation"]
structure Approximation (K : System f) (n : ℕ+) where
  /-- The later positive exact exponent. -/
  N : ℕ+
  /-- The requested exponent is no larger than the later exponent. -/
  le : n ≤ N
  /-- A Tate resolution of the later finite-power quotient with no degree-zero variables. -/
  resolution : Resolution.{u, x} f N
  /-- The positive generators of the resolution are finite in every degree. -/
  finite : resolution.HasFinitePositiveGenerators
  /-- The comparison from the later powered Koszul stage. -/
  fromKoszul : K.stage N ⟶ resolution.algebra
  /-- The comparison to the requested powered Koszul stage. -/
  toKoszul : resolution.algebra ⟶ K.stage n
  /-- The later Koszul comparison followed by the Tate augmentation is the canonical quotient
  augmentation. -/
  fromKoszul_augmentation : FromKoszul.IsCanonical K (A := resolution) fromKoszul
  /-- The two Koszul comparisons compose to the canonical exact-power transition. -/
  fromKoszul_toKoszul :
    Comparison.FactorsTransition K le fromKoszul toKoszul
  /-- On zeroth homology, the map to the requested Koszul stage induces the canonical transition
  between finite-power quotients. -/
  toKoszul_commutesOnH0 : ToKoszul.InducesQuotient K le (A := resolution) toKoszul

namespace Approximation

variable {K : System f} {n : ℕ+}

/-- Degree zero of a powered Koszul--Tate approximation is canonically the base ring. -/
@[stacks 0GZ4 "degree zero of a powered Koszul--Tate approximation"]
theorem degreeZeroIsBase (A : Approximation.{u, x} K n) :
    A.resolution.algebra.toChainDGAlgebra.DegreeZeroIsBase := sorry

/-- The augmentation of a powered Koszul--Tate approximation is a genuine quasi-isomorphism. -/
@[stacks 0GZ4 "quasi-isomorphism of a powered Koszul--Tate approximation"]
theorem augmentation_quasiIso (A : Approximation.{u, x} K n) :
    QuasiIso A.resolution.augmentation.toChainMap := sorry

/-- Over a Noetherian ring, the canonical powered Koszul divided-power stage admits a finite-cell
Tate approximation from a later exact-power stage. -/
@[stacks 0GZ4 "canonical powered Koszul--Tate approximation"]
theorem nonempty_canonical [IsNoetherianRing R] (f : ι → R) (n : ℕ+) :
    Nonempty (Approximation.{u, x} (KoszulComplex.DP.system f) n) := sorry

end Approximation

end KoszulComplex.Tate
