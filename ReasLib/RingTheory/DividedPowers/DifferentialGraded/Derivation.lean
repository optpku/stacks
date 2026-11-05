/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.Predifferential
public import ReasLib.RingTheory.DividedPowers.DifferentialGraded.ChainAlgebra
public import ReasLib.RingTheory.DividedPowers.GradedAlgebra.Predifferential

/-!
# Degree-two derivations of divided-power chain algebras

The canonical divided-power refinement is owned by
`DividedPowerGradedAlgebra`. This file gives its native chain-DGA presentation and an explicit
equivalence with the canonical owner on `A.toGradedAlgebra`. In the homological
grading convention, the source's degree-two derivations lower degree by two, so their reusable
graded-algebra model has degree `-2`.
-/

@[expose] public section

noncomputable section

universe u v

open ChainGradedAlgebra

namespace DividedPowerChainAlgebra

variable {R : Type u} [CommRing R]

/-- The chain-graded algebra underlying a divided-power chain algebra. -/
abbrev toChainGradedAlgebra (A : DividedPowerChainAlgebra.{u, v} R) :
    ChainGradedAlgebra.{u, v} R :=
  A.toChainDGAlgebra.toChainGradedAlgebra

/-- The canonical predifferential on the underlying chain-graded algebra. -/
abbrev predifferential (A : DividedPowerChainAlgebra.{u, v} R) :
    Predifferential A.toChainGradedAlgebra :=
  A.toChainDGAlgebra.predifferential

/-- Identify the extension-by-zero grading with the original nonnegative chain grading.
The maps are identities in natural degrees and the unique zero maps in negative degrees. -/
def gradedPieceEquiv (A : DividedPowerChainAlgebra.{u, v} R) :
    ∀ i : ℤ, A.toGradedAlgebra.toChainGradedAlgebra.X i ≃ₗ[R]
      A.toChainGradedAlgebra.X i
  | .ofNat _ => LinearEquiv.refl R _
  | .negSucc n => by
    letI := ModuleCat.subsingleton_of_isZero
      (A.toChainDGAlgebra.isZero_X_of_neg (.negSucc n) (by omega))
    change PUnit ≃ₗ[R] A.toChainDGAlgebra.X (.negSucc n)
    exact LinearEquiv.ofSubsingleton _ _

/-- The comparison is the identity on every nonnegative piece. -/
@[simp]
theorem gradedPieceEquiv_ofNat (A : DividedPowerChainAlgebra.{u, v} R) (n : ℕ)
    (x : A.toGradedAlgebra.toGradedAlgebra.piece n) :
    A.gradedPieceEquiv n x = x := rfl

/-- The comparison respects homogeneous multiplication. -/
theorem gradedPieceEquiv_mul (A : DividedPowerChainAlgebra.{u, v} R)
    (i j : ℤ) (x : A.toGradedAlgebra.toChainGradedAlgebra.X i)
    (y : A.toGradedAlgebra.toChainGradedAlgebra.X j) :
    A.gradedPieceEquiv (i + j) (A.toGradedAlgebra.toChainGradedAlgebra.mul i j x y) =
      A.toChainGradedAlgebra.mul i j (A.gradedPieceEquiv i x) (A.gradedPieceEquiv j y) := by
  cases i with
  | ofNat i =>
    cases j with
    | ofNat j => rfl
    | negSucc j =>
      have hy : y = 0 := by
        change (y : PUnit) = 0
        exact (inferInstance : Subsingleton PUnit).elim _ _
      simp only [hy, map_zero]
  | negSucc i =>
    have hx : x = 0 := by
      change (x : PUnit) = 0
      exact (inferInstance : Subsingleton PUnit).elim _ _
    simp only [hx, map_zero, LinearMap.zero_apply]

/-- The inverse comparison respects homogeneous multiplication. -/
theorem gradedPieceEquiv_symm_mul (A : DividedPowerChainAlgebra.{u, v} R)
    (i j : ℤ) (x : A.toChainGradedAlgebra.X i) (y : A.toChainGradedAlgebra.X j) :
    (A.gradedPieceEquiv (i + j)).symm (A.toChainGradedAlgebra.mul i j x y) =
      A.toGradedAlgebra.toChainGradedAlgebra.mul i j
        ((A.gradedPieceEquiv i).symm x) ((A.gradedPieceEquiv j).symm y) := by
  apply (A.gradedPieceEquiv (i + j)).injective
  simp only [LinearEquiv.apply_symm_apply, gradedPieceEquiv_mul]

/-- Transport a native chain derivation to the canonical divided-power graded algebra. -/
def toGradedDerivation (A : DividedPowerChainAlgebra.{u, v} R) {k : ℤ}
    (D : Derivation A.toChainGradedAlgebra k) :
    Derivation A.toGradedAlgebra.toChainGradedAlgebra k :=
  Derivation.transport (fun i ↦ (A.gradedPieceEquiv i).symm) A.gradedPieceEquiv_symm_mul D

/-- Transport back to the native chain grading using the explicit inverse comparison. -/
def ofGradedDerivation (A : DividedPowerChainAlgebra.{u, v} R) {k : ℤ}
    (D : Derivation A.toGradedAlgebra.toChainGradedAlgebra k) :
    Derivation A.toChainGradedAlgebra k :=
  Derivation.transport A.gradedPieceEquiv A.gradedPieceEquiv_mul D

@[simp]
theorem ofGradedDerivation_toGradedDerivation (A : DividedPowerChainAlgebra.{u, v} R)
    {k : ℤ} (D : Derivation A.toChainGradedAlgebra k) :
    A.ofGradedDerivation (A.toGradedDerivation D) = D := by
  apply Subtype.ext
  exact HomogeneousMap.conj_symm_conj (fun i ↦ (A.gradedPieceEquiv i).symm) D.1

@[simp]
theorem toGradedDerivation_ofGradedDerivation (A : DividedPowerChainAlgebra.{u, v} R)
    {k : ℤ} (D : Derivation A.toGradedAlgebra.toChainGradedAlgebra k) :
    A.toGradedDerivation (A.ofGradedDerivation D) = D := by
  apply Subtype.ext
  exact HomogeneousMap.conj_symm_conj A.gradedPieceEquiv D.1

/-- Transport preserves and reflects closedness under a reference predifferential. -/
theorem toGradedDerivation_isClosed_iff (A : DividedPowerChainAlgebra.{u, v} R) {k : ℤ}
    (D : Derivation A.toChainGradedAlgebra k) (d : Predifferential A.toChainGradedAlgebra) :
    Derivation.IsClosed (A.toGradedDerivation D) (A.toGradedDerivation d) ↔
      Derivation.IsClosed D d :=
  HomogeneousMap.conj_gradedCommutes_iff (fun i ↦ (A.gradedPieceEquiv i).symm) D.1 d.1

/-- Evaluation of the transported derivation is explicit degreewise conjugation. -/
theorem toGradedDerivation_apply (A : DividedPowerChainAlgebra.{u, v} R) {k : ℤ}
    (D : Derivation A.toChainGradedAlgebra k) (i : ℤ)
    (x : A.toGradedAlgebra.toChainGradedAlgebra.X i) :
    Derivation.toHomogeneousMap (A.toGradedDerivation D) i x =
      (A.gradedPieceEquiv (i + k)).symm
        (Derivation.toHomogeneousMap D i (A.gradedPieceEquiv i x)) := rfl

/-- The chain specialization of the canonical divided-power compatibility predicate.
Transport uses identity maps in nonnegative degrees and the explicit zero equivalences in
negative degrees; no new compatibility law is owned here. -/
abbrev PreservesDP (A : DividedPowerChainAlgebra.{u, v} R) {k : ℤ}
    (D : Derivation A.toChainGradedAlgebra k) : Prop :=
  A.toGradedAlgebra.PreservesDP (A.toGradedDerivation D)

/-- The stated bridge to the canonical graded owner is definitional. -/
theorem preservesDP_iff_toGradedAlgebra (A : DividedPowerChainAlgebra.{u, v} R) {k : ℤ}
    (D : Derivation A.toChainGradedAlgebra k) :
    A.PreservesDP D ↔ A.toGradedAlgebra.PreservesDP (A.toGradedDerivation D) := Iff.rfl

/-- The transported predicate is exactly the original formula in the native chain modules.
Positive `n` includes `n = 1`; the input degree is positive and even. -/
theorem preservesDP_iff (A : DividedPowerChainAlgebra.{u, v} R) {k : ℤ}
    (D : Derivation A.toChainGradedAlgebra k) :
    A.PreservesDP D ↔
      ∀ (n : ℕ+) (d : ℕ) (x : A.toChainDGAlgebra.nonnegativePiece (2 * (d + 1))),
        D (2 * ((n : ℕ) * (d + 1)) : ℕ) (A.gamma.gammaPiece (n : ℕ) d x) =
          A.toChainGradedAlgebra.reindex (DividedPowerGradedAlgebra.preservesDPIndex k n d)
            (A.toChainGradedAlgebra.mul _ _ (D (2 * (d + 1) : ℕ) x)
              (A.gamma.gammaPiece ((n : ℕ) - 1) d x)) := by
  have left (n : ℕ+) (d : ℕ)
      (x : A.toChainDGAlgebra.nonnegativePiece (2 * (d + 1))) :
      A.gradedPieceEquiv (((2 * ((n : ℕ) * (d + 1)) : ℕ) : ℤ) + k)
          (A.toGradedAlgebra.derivationPiece (A.toGradedDerivation D)
            (A.gamma.gammaPiece (n : ℕ) d x)) =
        D (2 * ((n : ℕ) * (d + 1)) : ℕ) (A.gamma.gammaPiece (n : ℕ) d x) := by
    change A.gradedPieceEquiv (((2 * ((n : ℕ) * (d + 1)) : ℕ) : ℤ) + k)
      ((A.gradedPieceEquiv (((2 * ((n : ℕ) * (d + 1)) : ℕ) : ℤ) + k)).symm
        (D (2 * ((n : ℕ) * (d + 1)) : ℕ)
          (A.gradedPieceEquiv (2 * ((n : ℕ) * (d + 1)) : ℕ)
            (A.gamma.gammaPiece (n : ℕ) d x)))) = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  have right (n : ℕ+) (d : ℕ)
      (x : A.toChainDGAlgebra.nonnegativePiece (2 * (d + 1))) :
      A.gradedPieceEquiv (((2 * ((n : ℕ) * (d + 1)) : ℕ) : ℤ) + k)
          (A.toGradedAlgebra.toChainGradedAlgebra.reindex
            (DividedPowerGradedAlgebra.preservesDPIndex k n d)
            (A.toGradedAlgebra.mulPieceRight
              (A.toGradedAlgebra.derivationPiece (A.toGradedDerivation D) x)
              (A.gamma.gammaPiece ((n : ℕ) - 1) d x))) =
        A.toChainGradedAlgebra.reindex (DividedPowerGradedAlgebra.preservesDPIndex k n d)
          (A.toChainGradedAlgebra.mul _ _ (D (2 * (d + 1) : ℕ) x)
            (A.gamma.gammaPiece ((n : ℕ) - 1) d x)) := by
    rw [HomogeneousMap.equiv_reindex]
    change A.toChainGradedAlgebra.reindex _
      (A.gradedPieceEquiv _ (A.toGradedAlgebra.toChainGradedAlgebra.mul _ _ _ _)) = _
    rw [gradedPieceEquiv_mul]
    change A.toChainGradedAlgebra.reindex _
      (A.toChainGradedAlgebra.mul _ _
        (A.gradedPieceEquiv (((2 * (d + 1) : ℕ) : ℤ) + k)
          ((A.gradedPieceEquiv (((2 * (d + 1) : ℕ) : ℤ) + k)).symm
            (D (2 * (d + 1) : ℕ) (A.gradedPieceEquiv (2 * (d + 1) : ℕ) x))))
        (A.gradedPieceEquiv (2 * (((n : ℕ) - 1) * (d + 1)) : ℕ)
          (A.gamma.gammaPiece ((n : ℕ) - 1) d x))) = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  constructor
  · intro h n d x
    exact (left n d x).symm.trans
      ((congrArg (A.gradedPieceEquiv _) (h n d x)).trans (right n d x))
  · intro h n d x
    apply (A.gradedPieceEquiv _).injective
    exact (left n d x).trans ((h n d x).trans (right n d x).symm)

/-- Squaring a predifferential commutes with transport to the canonical grading. -/
theorem toGradedDerivation_square (A : DividedPowerChainAlgebra.{u, v} R)
    (d : Predifferential A.toChainGradedAlgebra) :
    A.toGradedDerivation (ChainGradedAlgebra.Predifferential.square d) =
      ChainGradedAlgebra.Predifferential.square (A.toGradedDerivation d) := by
  apply Subtype.ext
  exact HomogeneousMap.conj_comp (fun i ↦ (A.gradedPieceEquiv i).symm) d.1 d.1

namespace PreservesDP

variable {A : DividedPowerChainAlgebra.{u, v} R}

/-- The square of a predifferential preserving divided powers again preserves divided powers. -/
theorem square (d : Predifferential A.toChainGradedAlgebra)
    (h : A.PreservesDP d) :
    A.PreservesDP (ChainGradedAlgebra.Predifferential.square d) := by
  change A.toGradedAlgebra.PreservesDP (A.toGradedDerivation
    (ChainGradedAlgebra.Predifferential.square d))
  rw [toGradedDerivation_square]
  exact DividedPowerGradedAlgebra.PreservesDP.square _ h

end PreservesDP

/-- The canonical predifferential of a divided-power chain algebra preserves its divided
powers, by the compatibility carried by the algebra. -/
theorem predifferential_preservesDP (A : DividedPowerChainAlgebra.{u, v} R) :
    A.PreservesDP A.predifferential := sorry

/-- The native chain presentation of the canonical graded `DPDerivation`.
It retains the original chain modules for evaluation. `DPDerivation.toGradedEquiv` identifies
this thin specialization with the canonical owner, for every reference predifferential. -/
structure DPDerivation (A : DividedPowerChainAlgebra.{u, v} R)
    (d : Predifferential A.toChainGradedAlgebra) (k : ℤ) where
  /-- The canonical divided-power derivation on the extension-by-zero grading. -/
  toGraded : A.toGradedAlgebra.DPDerivation (A.toGradedDerivation d) k

/-- Section 23.7 (Tag 09PR): a degree-two derivation is the canonical specialization of a
divided-power derivation to the chain differential and homological shift `-2`. -/
@[stacks 09PR "degree-two derivations compatible with divided powers"]
abbrev DegreeTwoDerivation (A : DividedPowerChainAlgebra.{u, v} R) :=
  DPDerivation A A.predifferential (-2)

namespace DPDerivation

variable {A : DividedPowerChainAlgebra.{u, v} R}
variable {d : Predifferential A.toChainGradedAlgebra} {k : ℤ}

/-- Evaluate the canonical data in the original chain grading. -/
def toDerivation (D : DPDerivation A d k) : Derivation A.toChainGradedAlgebra k :=
  A.ofGradedDerivation D.toGraded.toDerivation

/-- The native derivation is closed under the specified predifferential. -/
theorem isClosed (D : DPDerivation A d k) : Derivation.IsClosed D.toDerivation d := by
  apply (A.toGradedDerivation_isClosed_iff _ d).1
  simpa only [toDerivation, toGradedDerivation_ofGradedDerivation] using D.toGraded.isClosed

/-- Preservation of divided powers is inherited from the canonical owner. -/
theorem preservesDP (D : DPDerivation A d k) : A.PreservesDP D.toDerivation := by
  change A.toGradedAlgebra.PreservesDP
    (A.toGradedDerivation (A.ofGradedDerivation D.toGraded.toDerivation))
  simpa only [toGradedDerivation_ofGradedDerivation] using D.toGraded.preservesDP

/-- A divided-power derivation acts on homogeneous elements with its specified degree shift. -/
instance : CoeFun (DPDerivation A d k) (fun _ ↦ ∀ i : ℤ,
    A.toChainGradedAlgebra.X i → A.toChainGradedAlgebra.X (i + k)) where
  coe D := D.toDerivation

/-- Evaluation of a divided-power derivation is evaluation of its underlying graded derivation. -/
@[simp] theorem coe_apply (D : DPDerivation A d k) (i : ℤ)
    (x : A.toChainGradedAlgebra.X i) :
    D i x = D.toDerivation i x := sorry

/-- A divided-power derivation graded-commutes with its specified predifferential. -/
theorem gradedCommutes_d (D : DPDerivation A d k) :
    HomogeneousMap.GradedCommutes (Derivation.toHomogeneousMap D.toDerivation)
      (Derivation.toHomogeneousMap d) := sorry

/-- A divided-power derivation satisfies the divided-power formula on positive-even homogeneous
inputs. This theorem can be applied directly as `D.map_gamma n d x`. -/
theorem map_gamma (D : DPDerivation A d k) :
    A.PreservesDP D.toDerivation := sorry

/-- Divided-power derivations are determined by their values on homogeneous elements. -/
@[ext] theorem ext {D E : DPDerivation A d k}
    (h : ∀ i : ℤ, ∀ x : A.toChainGradedAlgebra.X i, D i x = E i x) : D = E := sorry

/-- The defining laws are closedness under the specified predifferential and preservation of
divided powers. -/
theorem laws_spec (D : DPDerivation A d k) :
    ChainGradedAlgebra.Derivation.IsClosed D.toDerivation d ∧
      A.PreservesDP D.toDerivation := sorry

/-- Equality of native divided-power derivations follows from equality of their data. -/
theorem ext_toDerivation {D E : DPDerivation A d k}
    (h : D.toDerivation = E.toDerivation) : D = E := by
  cases D with
  | mk D =>
    cases E with
    | mk E =>
      congr 1
      apply DividedPowerGradedAlgebra.DPDerivation.ext_toDerivation
      have h' := congrArg A.toGradedDerivation h
      simpa only [toDerivation, toGradedDerivation_ofGradedDerivation] using h'

/-- The chain wrapper and the canonical owner have exactly the same data. -/
def toGradedEquiv : DPDerivation A d k ≃
    A.toGradedAlgebra.DPDerivation (A.toGradedDerivation d) k where
  toFun := DPDerivation.toGraded
  invFun := DPDerivation.mk
  left_inv D := by cases D; rfl
  right_inv _ := rfl

/-- The bridge transports the native underlying derivation as stated. -/
@[simp]
theorem toGradedEquiv_toDerivation (D : DPDerivation A d k) :
    (toGradedEquiv D).toDerivation = A.toGradedDerivation D.toDerivation :=
  (A.toGradedDerivation_ofGradedDerivation D.toGraded.toDerivation).symm

/-- The square of a divided-power-compatible predifferential, bundled as a degree-`-2`
divided-power derivation closed under that predifferential. -/
def square (d : Predifferential A.toChainGradedAlgebra) (h : A.PreservesDP d) :
    DPDerivation A d (-2) where
  toGraded := DividedPowerGradedAlgebra.DPDerivation.square
    ⟨A.toGradedDerivation d, h⟩

/-- The native square retains the original square derivation. -/
@[simp]
theorem square_toDerivation (d : Predifferential A.toChainGradedAlgebra)
    (h : A.PreservesDP d) :
    (square d h).toDerivation = ChainGradedAlgebra.Predifferential.square d := by
  change A.ofGradedDerivation
    (ChainGradedAlgebra.Predifferential.square (A.toGradedDerivation d)) = _
  rw [← toGradedDerivation_square, ofGradedDerivation_toGradedDerivation]

end DPDerivation

namespace DegreeTwoDerivation

variable {A : DividedPowerChainAlgebra.{u, v} R}

/-- A canonical degree-two derivation satisfies the ordinary Leibniz rule because its degree
shift is even. -/
theorem leibniz_apply (D : DegreeTwoDerivation A) (i j : ℤ)
    (x : A.toChainGradedAlgebra.X i) (y : A.toChainGradedAlgebra.X j) :
    D (i + j) (A.toChainGradedAlgebra.mul i j x y) =
      A.toChainGradedAlgebra.reindex (add_right_comm i (-2) j)
          (A.toChainGradedAlgebra.mul (i + (-2)) j (D i x) y) +
        A.toChainGradedAlgebra.reindex (add_assoc i j (-2)).symm
          (A.toChainGradedAlgebra.mul i (j + (-2)) x (D j y)) := sorry

/-- A canonical degree-two derivation commutes ordinarily with the chain differential. -/
theorem commutes_d (D : DegreeTwoDerivation A) :
    HomogeneousMap.Commutes (Derivation.toHomogeneousMap D.toDerivation)
      (Derivation.toHomogeneousMap A.predifferential) := sorry

/-- A canonical degree-two derivation satisfies the divided-power formula. -/
theorem map_gamma (D : DegreeTwoDerivation A) :
    A.PreservesDP D.toDerivation := sorry

end DegreeTwoDerivation

end DividedPowerChainAlgebra
