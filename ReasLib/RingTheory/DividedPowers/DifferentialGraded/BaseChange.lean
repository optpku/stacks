/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DividedPowers.Derivation
public import ReasLib.RingTheory.DividedPowers.Extension
public import ReasLib.RingTheory.DividedPowers.DifferentialGraded.ChainAlgebra
public import ReasLib.RingTheory.DividedPowers.GradedAlgebra.BaseChange
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Base change of derivations and compatible divided powers

The chain-DGA layer records scalar extension degreewise, including multiplication, differential,
and divided-power formulas. The independent ideal-theoretic API under `Derivation` and
`DividedPowers.Extension` remains available as a lower-level specialization.
-/

@[expose] public section

noncomputable section

universe uR uR' uA

open scoped TensorProduct
open CategoryTheory

namespace Derivation

section

variable {R : Type uR} {R' : Type uR'} {A : Type uA}
variable [CommRing R] [CommRing R'] [CommRing A] [Algebra R A] [Algebra R R']

/-- The scalar extension of a derivation's underlying linear map to `R' ⊗[R] A`. -/
abbrev baseChangeLinearMap (d : Derivation R A A) :
    TensorProduct R R' A →ₗ[R'] TensorProduct R R' A :=
  LinearMap.baseChange R' (d : A →ₗ[R] A)

/-- The scalar-extended linear map annihilates the unit. -/
theorem baseChangeLinearMap_one (d : Derivation R A A) :
    d.baseChangeLinearMap (R' := R') (1 : TensorProduct R R' A) = 0 := sorry

/-- The scalar-extended linear map satisfies the Leibniz rule. -/
theorem baseChangeLinearMap_leibniz (d : Derivation R A A)
    (x y : TensorProduct R R' A) :
    d.baseChangeLinearMap (R' := R') (x * y) =
      x • d.baseChangeLinearMap (R' := R') y +
        y • d.baseChangeLinearMap (R' := R') x := sorry

/-- The scalar extension of a derivation to `R' ⊗[R] A`. -/
def baseChange (d : Derivation R A A) :
    Derivation R' (TensorProduct R R' A) (TensorProduct R R' A) :=
  Derivation.mk d.baseChangeLinearMap
    (d.baseChangeLinearMap_one (R' := R'))
    (d.baseChangeLinearMap_leibniz (R' := R'))

/-- Scalar extension applies the original derivation to the right factor of a pure tensor. -/
theorem baseChange_tmul (d : Derivation R A A) (r : R') (x : A) :
    d.baseChange (R' := R') (r ⊗ₜ[R] x) = r ⊗ₜ[R] d x := sorry

end

end Derivation

namespace DividedPowers

section

variable {R : Type uR} {R' : Type uR'} {A : Type uA}
variable [CommRing R] [CommRing R'] [CommRing A] [Algebra R A] [Algebra R R']
variable {I : Ideal A} {gamma : DividedPowers I}

/-- The canonical ring map from an algebra to its scalar extension. -/
abbrev baseChangeMap : A →+* TensorProduct R R' A :=
  (Algebra.TensorProduct.includeRight : A →ₐ[R] TensorProduct R R' A).toRingHom

/-- An extension of divided powers is compatible with base change when its divided powers are
compatible with the scalar-extended derivation. -/
def Extension.IsCompatibleBaseChange
    (h : gamma.Extension (baseChangeMap (R := R) (R' := R') (A := A)))
    (d : Derivation R A A) : Prop :=
  h.dividedPowers.IsCompatibleWith (d.baseChange (R' := R'))

/-- Compatible base-change data satisfy the expected formula on pure tensors. -/
theorem Extension.dpow_tmul
    (h : gamma.Extension (baseChangeMap (R := R) (R' := R') (A := A)))
    (n : ℕ) (r : R') {x : A} (hx : x ∈ I) :
    h.dividedPowers.dpow n (r ⊗ₜ[R] x) =
      r ^ n • (1 ⊗ₜ[R] gamma.dpow n x) := sorry

/-- Compatible divided powers on an ordinary ideal extend along scalar extension and remain
compatible with the base-changed derivation. -/
theorem exists_compatibleBaseChange
    (gamma : DividedPowers I) (d : Derivation R A A) [gamma.IsCompatibleWith d] :
    ∃ h : gamma.Extension (baseChangeMap (R := R) (R' := R') (A := A)),
      h.IsCompatibleBaseChange d := sorry

end

end DividedPowers

namespace DividedPowerChainAlgebra

section

variable {R : Type uR} {R' : Type uR'}
variable [CommRing R] [CommRing R'] [Algebra R R']

/-- A scalar-extension model of a divided-power chain DGA. Its homogeneous pieces are explicitly
identified with `R' ⊗[R] A_n`, and every structure map satisfies the expected pure-tensor formula.
-/
@[stacks 09PL "base-change model"]
structure BaseChange (A : DividedPowerChainAlgebra.{uR, uA} R) where
  /-- The scalar-extended divided-power chain DGA. -/
  algebra : DividedPowerChainAlgebra.{uR', uA} R'
  /-- The canonical scalar-extension identification in every nonnegative degree. -/
  pieceIso (n : ℕ) :
    (R' ⊗[R] A.toChainDGAlgebra.nonnegativePiece n) ≃ₗ[R']
      algebra.toChainDGAlgebra.nonnegativePiece n
  /-- The tensor of the original unit is the unit after base change. -/
  map_one : pieceIso 0 (1 ⊗ₜ[R] A.toChainDGAlgebra.one) =
    algebra.toChainDGAlgebra.one
  /-- Homogeneous multiplication is the scalar extension of the original multiplication. -/
  map_mul (n m : ℕ) (r s : R')
      (x : A.toChainDGAlgebra.nonnegativePiece n)
      (y : A.toChainDGAlgebra.nonnegativePiece m) :
    pieceIso (n + m) ((r * s) ⊗ₜ[R] A.toChainDGAlgebra.nonnegativeMul x y) =
      algebra.toChainDGAlgebra.nonnegativeMul
        (pieceIso n (r ⊗ₜ[R] x)) (pieceIso m (s ⊗ₜ[R] y))
  /-- The differential acts on the original homogeneous factor of a pure tensor. -/
  map_d (n : ℕ+) (r : R') (x : A.toChainDGAlgebra.nonnegativePiece n) :
    algebra.toChainDGAlgebra.nonnegativeDifferential n (pieceIso n (r ⊗ₜ[R] x)) =
      pieceIso ((n : ℕ) - 1)
        (r ⊗ₜ[R] A.toChainDGAlgebra.nonnegativeDifferential n x)
  /-- Divided powers satisfy `γ_n(r ⊗ x) = r^n ⊗ γ_n(x)` on homogeneous positive-even inputs. -/
  map_gamma (n d : ℕ) (r : R')
      (x : A.toChainDGAlgebra.nonnegativePiece (2 * (d + 1))) :
    algebra.gamma.gammaPiece n d
        (pieceIso (2 * (d + 1)) (r ⊗ₜ[R] x)) =
      pieceIso (2 * (n * (d + 1)))
        ((r ^ n) ⊗ₜ[R] A.gamma.gammaPiece n d x)

namespace BaseChange

variable {A : DividedPowerChainAlgebra.{uR, uA} R}

/-- Forgetting the differential from a chain-DGA base-change model gives the underlying
divided-power graded base-change model. -/
@[stacks 09PL "underlying graded base-change model"]
def toGraded (X : BaseChange (R' := R') A) :
    A.toGradedAlgebra.BaseChange (S := R') where
  algebra := X.algebra.toGradedAlgebra
  pieceIso := X.pieceIso
  map_one := X.map_one
  map_mul := X.map_mul
  map_gamma := X.map_gamma

/-- The canonical comparison on each homogeneous piece of two scalar-extension models. -/
def comparisonPiece (X Y : BaseChange (R' := R') A) (n : ℕ) :
    X.algebra.toChainDGAlgebra.nonnegativePiece n ≃ₗ[R']
      Y.algebra.toChainDGAlgebra.nonnegativePiece n :=
  (X.pieceIso n).symm.trans (Y.pieceIso n)

/-- The homogeneous comparison from a base-change model to itself is the identity. -/
theorem comparisonPiece_self (X : BaseChange (R' := R') A) (n : ℕ) :
    X.comparisonPiece X n = LinearEquiv.refl R' _ := sorry

/-- Homogeneous comparisons between base-change models compose transitively. -/
theorem comparisonPiece_trans (X Y Z : BaseChange (R' := R') A) (n : ℕ) :
    (X.comparisonPiece Y n).trans (Y.comparisonPiece Z n) =
      X.comparisonPiece Z n := sorry

/-- The base-change comparison preserves the graded unit. -/
theorem comparisonPiece_one (X Y : BaseChange (R' := R') A) :
    X.comparisonPiece Y 0 X.algebra.toChainDGAlgebra.one =
      Y.algebra.toChainDGAlgebra.one := sorry

/-- The base-change comparison preserves homogeneous multiplication. -/
theorem comparisonPiece_mul (X Y : BaseChange (R' := R') A) (n m : ℕ)
    (x : X.algebra.toChainDGAlgebra.nonnegativePiece n)
    (y : X.algebra.toChainDGAlgebra.nonnegativePiece m) :
    X.comparisonPiece Y (n + m) (X.algebra.toChainDGAlgebra.nonnegativeMul x y) =
      Y.algebra.toChainDGAlgebra.nonnegativeMul
        (X.comparisonPiece Y n x) (X.comparisonPiece Y m y) := sorry

/-- The degreewise comparison of two base-change models as a graded-algebra homomorphism. -/
def gradedComparison (X Y : BaseChange (R' := R') A) :
    X.algebra.toChainDGAlgebra.nonnegativePart ⟶
      Y.algebra.toChainDGAlgebra.nonnegativePart where
  map n := (X.comparisonPiece Y n).toLinearMap
  map_one := X.comparisonPiece_one Y
  map_mul := X.comparisonPiece_mul Y

/-- The graded comparison from a base-change model to itself is the identity. -/
theorem gradedComparison_self (X : BaseChange (R' := R') A) :
    X.gradedComparison X = 𝟙 X.algebra.toChainDGAlgebra.nonnegativePart := sorry

/-- Graded comparisons between base-change models compose transitively. -/
theorem gradedComparison_comp (X Y Z : BaseChange (R' := R') A) :
    X.gradedComparison Y ≫ Y.gradedComparison Z = X.gradedComparison Z := sorry

/-- The graded comparison preserves the base-changed divided powers. -/
theorem gradedComparison_map_gamma (X Y : BaseChange (R' := R') A) (n : ℕ)
    (x : X.algebra.toChainDGAlgebra.nonnegativePart.evenPositivePart) :
    (X.gradedComparison Y).evenMap (X.algebra.gamma n x) =
      Y.algebra.gamma n ((X.gradedComparison Y).evenPositiveMap x) := sorry

/-- The canonical divided-power graded-algebra comparison between two base-change models. -/
def dpComparison (X Y : BaseChange (R' := R') A) :
    X.algebra.toGradedAlgebra ⟶ Y.algebra.toGradedAlgebra where
  toGradedHom := X.gradedComparison Y
  map_gamma := X.gradedComparison_map_gamma Y

/-- The graded comparison underlying a chain-DGA base-change model is the canonical comparison
of its underlying graded base-change models. -/
theorem toGraded_comparison (X Y : BaseChange (R' := R') A) :
    X.toGraded.comparison Y.toGraded = X.dpComparison Y := sorry

/-- Forgetting divided powers from the graded comparison recovers the explicit graded-algebra
comparison. -/
@[simp]
theorem dpComparison_toGradedHom (X Y : BaseChange (R' := R') A) :
    (X.dpComparison Y).toGradedHom = X.gradedComparison Y := sorry

/-- The divided-power graded comparison from a base-change model to itself is the identity. -/
@[simp]
theorem dpComparison_self (X : BaseChange (R' := R') A) :
    X.dpComparison X = 𝟙 X.algebra.toGradedAlgebra := sorry

/-- Divided-power graded comparisons between base-change models compose transitively. -/
@[simp]
theorem dpComparison_comp (X Y Z : BaseChange (R' := R') A) :
    X.dpComparison Y ≫ Y.dpComparison Z = X.dpComparison Z := sorry

/-- The explicit homogeneous linear map underlying the comparison of two base-change models.
It uses the tensor-product comparison in nonnegative degrees and the zero map in negative
degrees, where both chain DGAs are supported trivially. -/
def comparisonLinearMap (X Y : BaseChange (R' := R') A) (n : ℤ) :
    X.algebra.toChainDGAlgebra.X n →ₗ[R'] Y.algebra.toChainDGAlgebra.X n :=
  if hn : 0 ≤ n then
    (ChainDGAlgebra.ModuleCat.castLinearMap Y.algebra.toChainDGAlgebra
      (Int.toNat_of_nonneg hn)).comp
      ((X.comparisonPiece Y n.toNat).toLinearMap.comp
        (ChainDGAlgebra.ModuleCat.castLinearMap X.algebra.toChainDGAlgebra
          (Int.toNat_of_nonneg hn).symm))
  else
    0

/-- In a natural degree, the homogeneous comparison is the tensor-product comparison. -/
theorem comparisonLinearMap_ofNat (X Y : BaseChange (R' := R') A) (n : ℕ) :
    X.comparisonLinearMap Y n = (X.comparisonPiece Y n).toLinearMap := sorry

/-- The explicit homogeneous comparisons commute with the chain differentials. -/
theorem comparisonLinearMap_comm (X Y : BaseChange (R' := R') A)
    (i j : ℤ) (hij : (ComplexShape.down ℤ).Rel i j) :
    ModuleCat.ofHom (X.comparisonLinearMap Y i) ≫
        Y.algebra.toChainDGAlgebra.toChainComplex.d i j =
      X.algebra.toChainDGAlgebra.toChainComplex.d i j ≫
        ModuleCat.ofHom (X.comparisonLinearMap Y j) := sorry

/-- The explicit chain map comparing two scalar-extension models. -/
def comparisonChainMap (X Y : BaseChange (R' := R') A) :
    X.algebra.toChainDGAlgebra.toChainComplex ⟶
      Y.algebra.toChainDGAlgebra.toChainComplex where
  f n := ModuleCat.ofHom (X.comparisonLinearMap Y n)
  comm' := X.comparisonLinearMap_comm Y

/-- The explicit comparison chain map preserves the homogeneous unit. -/
theorem comparisonChainMap_one (X Y : BaseChange (R' := R') A) :
    (X.comparisonChainMap Y).f 0 X.algebra.toChainDGAlgebra.one =
      Y.algebra.toChainDGAlgebra.one := sorry

/-- The explicit comparison chain map preserves homogeneous multiplication. -/
theorem comparisonChainMap_mul (X Y : BaseChange (R' := R') A) (n m : ℤ)
    (x : X.algebra.toChainDGAlgebra.X n) (y : X.algebra.toChainDGAlgebra.X m) :
    (X.comparisonChainMap Y).f (n + m) (X.algebra.toChainDGAlgebra.mul n m x y) =
      Y.algebra.toChainDGAlgebra.mul n m
        ((X.comparisonChainMap Y).f n x) ((X.comparisonChainMap Y).f m y) := sorry

/-- The explicit chain-DGA comparison between two scalar-extension models. -/
def comparisonChainHom (X Y : BaseChange (R' := R') A) :
    ChainDGAlgebra.Hom X.algebra.toChainDGAlgebra Y.algebra.toChainDGAlgebra where
  toChainMap := X.comparisonChainMap Y
  map_one := X.comparisonChainMap_one Y
  map_mul := X.comparisonChainMap_mul Y

/-- The explicit chain-DGA comparison preserves the base-changed divided powers. -/
theorem comparisonChainHom_map_gamma (X Y : BaseChange (R' := R') A) (n : ℕ)
    (x : X.algebra.toChainDGAlgebra.nonnegativePart.evenPositivePart) :
    (X.comparisonChainHom Y).nonnegativePart.evenMap (X.algebra.gamma n x) =
      Y.algebra.gamma n
        ((X.comparisonChainHom Y).nonnegativePart.evenPositiveMap x) := sorry

/-- The canonical divided-power chain-DGA comparison between two scalar-extension models. -/
def chainComparison (X Y : BaseChange (R' := R') A) :
    X.algebra ⟶ Y.algebra where
  toChainHom := X.comparisonChainHom Y
  map_gamma := X.comparisonChainHom_map_gamma Y

/-- Forgetting divided powers from the canonical comparison recovers the explicit chain-DGA
comparison. -/
@[simp]
theorem chainComparison_toChainHom (X Y : BaseChange (R' := R') A) :
    (X.chainComparison Y).toChainHom = X.comparisonChainHom Y := sorry

/-- The canonical comparison acts in every integer degree by the explicit homogeneous linear
comparison. -/
@[simp]
theorem chainComparison_apply_int (X Y : BaseChange (R' := R') A) (i : ℤ)
    (x : X.algebra.toChainDGAlgebra.X i) :
    (X.chainComparison Y).toChainHom i x = X.comparisonLinearMap Y i x := sorry

/-- A divided-power chain-DGA map agrees with the canonical comparison when it induces the
degreewise tensor-product comparison in every nonnegative degree. -/
def AgreesOnPieces (X Y : BaseChange (R' := R') A)
    (f : X.algebra ⟶ Y.algebra) : Prop :=
  ∀ (n : ℕ) (x : X.algebra.toChainDGAlgebra.nonnegativePiece n),
    f.toChainHom.toChainMap.f (n : ℤ) x = X.comparisonPiece Y n x

/-- The canonical chain comparison agrees with the tensor-product comparison on every
nonnegative homogeneous piece. -/
theorem chainComparison_agrees (X Y : BaseChange (R' := R') A) :
    X.AgreesOnPieces Y (X.chainComparison Y) := sorry

/-- The canonical chain comparison acts by the degreewise tensor-product comparison. -/
theorem chainComparison_apply (X Y : BaseChange (R' := R') A) (n : ℕ)
    (x : X.algebra.toChainDGAlgebra.nonnegativePiece n) :
    (X.chainComparison Y).toChainHom.toChainMap.f (n : ℤ) x =
      X.comparisonPiece Y n x := sorry

/-- Any divided-power chain-DGA map agreeing on the scalar-extended pieces is the canonical
comparison. -/
theorem chainComparison_unique (X Y : BaseChange (R' := R') A)
    (f : X.algebra ⟶ Y.algebra) (hf : X.AgreesOnPieces Y f) :
    f = X.chainComparison Y := sorry

/-- There is a unique divided-power chain-DGA comparison inducing the tensor-product comparison
on every nonnegative homogeneous piece. -/
theorem existsUnique_chainComparison (X Y : BaseChange (R' := R') A) :
    ∃! f : X.algebra ⟶ Y.algebra, X.AgreesOnPieces Y f := sorry

/-- Restricting the chain-DGA comparison to the nonnegative graded algebra recovers the explicit
divided-power graded comparison. -/
theorem chainComparison_toGradedHom (X Y : BaseChange (R' := R') A) :
    (X.chainComparison Y).toGradedHom = X.dpComparison Y := sorry

/-- The canonical comparison from a base-change model to itself is the identity. -/
@[simp]
theorem chainComparison_self (X : BaseChange (R' := R') A) :
    X.chainComparison X = 𝟙 X.algebra := sorry

/-- Canonical comparisons between base-change models compose transitively. -/
@[simp]
theorem chainComparison_comp (X Y Z : BaseChange (R' := R') A) :
    X.chainComparison Y ≫ Y.chainComparison Z = X.chainComparison Z := sorry

/-- The forward and backward comparisons between two base-change models compose to the identity
on the source model. -/
theorem chainComparison_hom_inv_id (X Y : BaseChange (R' := R') A) :
    X.chainComparison Y ≫ Y.chainComparison X = 𝟙 X.algebra := sorry

/-- The backward and forward comparisons between two base-change models compose to the identity
on the target model. -/
theorem chainComparison_inv_hom_id (X Y : BaseChange (R' := R') A) :
    Y.chainComparison X ≫ X.chainComparison Y = 𝟙 Y.algebra := sorry

/-- The canonical isomorphism between two scalar-extension models. -/
@[stacks 09PL "canonical scalar-extension comparison"]
def comparisonIso (X Y : BaseChange (R' := R') A) : X.algebra ≅ Y.algebra where
  hom := X.chainComparison Y
  inv := Y.chainComparison X
  hom_inv_id := X.chainComparison_hom_inv_id Y
  inv_hom_id := X.chainComparison_inv_hom_id Y

/-- The forward map of the canonical base-change isomorphism is the canonical comparison. -/
@[simp]
theorem comparisonIso_hom (X Y : BaseChange (R' := R') A) :
    (X.comparisonIso Y).hom = X.chainComparison Y := sorry

/-- The inverse map of the canonical base-change isomorphism is the reverse comparison. -/
@[simp]
theorem comparisonIso_inv (X Y : BaseChange (R' := R') A) :
    (X.comparisonIso Y).inv = Y.chainComparison X := sorry

/-- The canonical isomorphism from a scalar-extension model to itself is the identity
isomorphism. -/
@[simp]
theorem comparisonIso_self (X : BaseChange (R' := R') A) :
    X.comparisonIso X = Iso.refl X.algebra := sorry

/-- Reversing a canonical scalar-extension isomorphism exchanges its two models. -/
@[simp]
theorem comparisonIso_symm (X Y : BaseChange (R' := R') A) :
    (X.comparisonIso Y).symm = Y.comparisonIso X := sorry

/-- Canonical scalar-extension isomorphisms compose transitively. -/
@[simp]
theorem comparisonIso_trans (X Y Z : BaseChange (R' := R') A) :
    (X.comparisonIso Y).trans (Y.comparisonIso Z) = X.comparisonIso Z := sorry

end BaseChange

/-- Lemma 23.6.7 (Tag 09PL): every compatible divided-power chain DGA admits a scalar-extension
model along a ring map. -/
@[stacks 09PL]
theorem nonemptyBaseChange (A : DividedPowerChainAlgebra.{uR, uA} R) :
    Nonempty (BaseChange (R' := R') A) := sorry

end

end DividedPowerChainAlgebra
