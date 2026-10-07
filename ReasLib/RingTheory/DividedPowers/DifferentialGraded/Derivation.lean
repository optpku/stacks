module

public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.Predifferential
public import ReasLib.RingTheory.DividedPowers.DifferentialGraded.ChainAlgebra

/-!
# Degree-two derivations of divided-power chain algebras

This file owns the divided-power refinement of a homogeneous derivation. In the homological
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

/-- The homogeneous degrees in the formula `D (γ n x) = D x * γ (n - 1) x` agree for a
derivation of arbitrary degree `k`. -/
theorem preservesDPIndex (k : ℤ) (n : ℕ+) (d : ℕ) :
    (((2 * (d + 1) : ℕ) : ℤ) + k) +
        ((2 * (((n : ℕ) - 1) * (d + 1)) : ℕ) : ℤ) =
      ((2 * ((n : ℕ) * (d + 1)) : ℕ) : ℤ) + k := sorry

/-- Restrict a homogeneous derivation to one naturally indexed nonnegative piece. -/
def derivationPiece (A : DividedPowerChainAlgebra.{u, v} R) {k : ℤ}
    (D : Derivation A.toChainGradedAlgebra k) {n : ℕ} :
    A.toChainDGAlgebra.nonnegativePiece n →ₗ[R]
      A.toChainGradedAlgebra.X ((n : ℤ) + k) :=
  Derivation.toHomogeneousMap D (n : ℤ)

/-- Restriction to a natural-degree piece evaluates the original homogeneous derivation. -/
@[simp] theorem derivationPiece_apply (A : DividedPowerChainAlgebra.{u, v} R) {k : ℤ}
    (D : Derivation A.toChainGradedAlgebra k) {n : ℕ}
    (x : A.toChainDGAlgebra.nonnegativePiece n) :
    A.derivationPiece D x = D (n : ℤ) x := sorry

/-- Multiply an integer-graded homogeneous element by an element of a naturally indexed
nonnegative piece. -/
def mulPieceRight (A : DividedPowerChainAlgebra.{u, v} R) {i : ℤ} {n : ℕ} :
    A.toChainGradedAlgebra.X i →ₗ[R]
      A.toChainDGAlgebra.nonnegativePiece n →ₗ[R]
        A.toChainGradedAlgebra.X (i + (n : ℤ)) :=
  A.toChainGradedAlgebra.mul i (n : ℤ)

/-- Mixed integer/natural-degree multiplication is the underlying graded multiplication. -/
@[simp] theorem mulPieceRight_apply (A : DividedPowerChainAlgebra.{u, v} R) {i : ℤ} {n : ℕ}
    (x : A.toChainGradedAlgebra.X i)
    (y : A.toChainDGAlgebra.nonnegativePiece n) :
    A.mulPieceRight x y = A.toChainGradedAlgebra.mul i (n : ℤ) x y := sorry

/-- A homogeneous graded derivation preserves divided powers when
`D (γ n x) = D x * γ (n - 1) x` on every positive-even homogeneous input. -/
def PreservesDP (A : DividedPowerChainAlgebra.{u, v} R) {k : ℤ}
    (D : Derivation A.toChainGradedAlgebra k) : Prop :=
  ∀ (n : ℕ+) (d : ℕ)
    (x : A.toChainDGAlgebra.nonnegativePiece (2 * (d + 1))),
    A.derivationPiece D (A.gamma.gammaPiece (n : ℕ) d x) =
      A.toChainGradedAlgebra.reindex (preservesDPIndex k n d)
        (A.mulPieceRight (A.derivationPiece D x)
          (A.gamma.gammaPiece ((n : ℕ) - 1) d x))

namespace PreservesDP

variable {A : DividedPowerChainAlgebra.{u, v} R}

/-- The square of a predifferential preserving divided powers again preserves divided powers. -/
theorem square (d : Predifferential A.toChainGradedAlgebra)
    (h : A.PreservesDP d) :
    A.PreservesDP (ChainGradedAlgebra.Predifferential.square d) := sorry

end PreservesDP

/-- The canonical predifferential of a divided-power chain algebra preserves its divided
powers, by the compatibility carried by the algebra. -/
theorem predifferential_preservesDP (A : DividedPowerChainAlgebra.{u, v} R) :
    A.PreservesDP A.predifferential := sorry

/-- A graded derivation preserving divided powers and closed under a specified predifferential. -/
structure DPDerivation (A : DividedPowerChainAlgebra.{u, v} R)
    (d : Predifferential A.toChainGradedAlgebra) (k : ℤ) where
  /-- The underlying homogeneous degree-`k` graded derivation. -/
  toDerivation : Derivation A.toChainGradedAlgebra k
  /-- The derivation is closed under `d`. -/
  isClosed : ChainGradedAlgebra.Derivation.IsClosed toDerivation d
  /-- The derivation preserves divided powers. -/
  preservesDP : A.PreservesDP toDerivation

/-- Section 23.7 (Tag 09PR): a degree-two derivation is the canonical specialization of a
divided-power derivation to the chain differential and homological shift `-2`. -/
@[stacks 09PR "degree-two derivations compatible with divided powers"]
abbrev DegreeTwoDerivation (A : DividedPowerChainAlgebra.{u, v} R) :=
  DPDerivation A A.predifferential (-2)

namespace DPDerivation

variable {A : DividedPowerChainAlgebra.{u, v} R}
variable {d : Predifferential A.toChainGradedAlgebra} {k : ℤ}

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

/-- The square of a divided-power-compatible predifferential, bundled as a degree-`-2`
divided-power derivation closed under that predifferential. -/
def square (d : Predifferential A.toChainGradedAlgebra) (h : A.PreservesDP d) :
    DPDerivation A d (-2) where
  toDerivation := ChainGradedAlgebra.Predifferential.square d
  isClosed := ChainGradedAlgebra.Predifferential.square_isClosed d
  preservesDP := PreservesDP.square d h

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
