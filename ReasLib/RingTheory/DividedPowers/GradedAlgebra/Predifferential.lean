/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.DirectSum.NonnegGradedAlgebra.Chain
public import ReasLib.Algebra.Homology.ChainGradedAlgebra.Predifferential
public import ReasLib.RingTheory.DividedPowers.GradedAlgebra.Category

/-!
# Predifferentials on divided-power graded algebras

Divided-power compatibility belongs to a graded algebra equipped with a predifferential; it does
not require the predifferential to square to zero.  This is the natural layer for deformation
lifts, where the lifted differential generally has nonzero square.  Genuine divided-power chain
algebras are specializations carrying an additional square-zero law.
-/

@[expose] public section

noncomputable section

universe u v

open ChainGradedAlgebra

namespace DividedPowerGradedAlgebra

variable {R : Type u} [CommRing R]

/-- The chain-graded algebra obtained by extending the underlying nonnegative graded algebra by
zero in negative degrees. -/
@[stacks 09PS "chain grading of a divided-power graded algebra"]
abbrev toChainGradedAlgebra (A : DividedPowerGradedAlgebra.{u, v} R) :
    ChainGradedAlgebra.{u, v} R :=
  A.toGradedAlgebra.toChainGradedAlgebra

/-- The homogeneous degrees in the divided-power derivation formula agree for an arbitrary
derivation degree. -/
theorem preservesDPIndex (k : ℤ) (n : ℕ+) (d : ℕ) :
    (((2 * (d + 1) : ℕ) : ℤ) + k) +
        ((2 * (((n : ℕ) - 1) * (d + 1)) : ℕ) : ℤ) =
      ((2 * ((n : ℕ) * (d + 1)) : ℕ) : ℤ) + k := by
  have hp : 2 * (d + 1) + 2 * (((n : ℕ) - 1) * (d + 1)) =
      2 * ((n : ℕ) * (d + 1)) := by
    rw [← Nat.mul_add]
    congr 1
    calc
      (d + 1) + ((n : ℕ) - 1) * (d + 1) =
          (((n : ℕ) - 1) + 1) * (d + 1) := by
        rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
      _ = (n : ℕ) * (d + 1) := by rw [Nat.sub_add_cancel n.pos]
  have hi := congrArg (fun m : ℕ ↦ (m : ℤ)) hp
  simp only [Nat.cast_add] at hi
  omega

/-- Restrict a homogeneous derivation to a naturally indexed nonnegative piece. -/
def derivationPiece (A : DividedPowerGradedAlgebra.{u, v} R) {k : ℤ}
    (D : Derivation A.toChainGradedAlgebra k) {n : ℕ} :
    A.toGradedAlgebra.piece n →ₗ[R] A.toChainGradedAlgebra.X ((n : ℤ) + k) :=
  Derivation.toHomogeneousMap D (n : ℤ)

/-- Restriction to a natural-degree piece evaluates the original homogeneous derivation. -/
@[simp]
theorem derivationPiece_apply (A : DividedPowerGradedAlgebra.{u, v} R) {k : ℤ}
    (D : Derivation A.toChainGradedAlgebra k) {n : ℕ}
    (x : A.toGradedAlgebra.piece n) :
    A.derivationPiece D x = D (n : ℤ) x := rfl

/-- Multiply an integer-graded homogeneous element by a naturally indexed nonnegative piece. -/
def mulPieceRight (A : DividedPowerGradedAlgebra.{u, v} R) {i : ℤ} {n : ℕ} :
    A.toChainGradedAlgebra.X i →ₗ[R] A.toGradedAlgebra.piece n →ₗ[R]
      A.toChainGradedAlgebra.X (i + (n : ℤ)) :=
  A.toChainGradedAlgebra.mul i (n : ℤ)

/-- Mixed integer/natural-degree multiplication is the underlying graded multiplication. -/
@[simp]
theorem mulPieceRight_apply (A : DividedPowerGradedAlgebra.{u, v} R)
    {i : ℤ} {n : ℕ} (x : A.toChainGradedAlgebra.X i)
    (y : A.toGradedAlgebra.piece n) :
    A.mulPieceRight x y = A.toChainGradedAlgebra.mul i (n : ℤ) x y := rfl

/-- A homogeneous derivation preserves divided powers when
`D (γ n x) = D x * γ (n - 1) x` on positive-even homogeneous inputs. -/
@[stacks 09PS "divided-power-compatible graded derivation"]
def PreservesDP (A : DividedPowerGradedAlgebra.{u, v} R) {k : ℤ}
    (D : Derivation A.toChainGradedAlgebra k) : Prop :=
  ∀ (n : ℕ+) (d : ℕ) (x : A.toGradedAlgebra.piece (2 * (d + 1))),
    A.derivationPiece D (A.gamma.gammaPiece (n : ℕ) d x) =
      A.toChainGradedAlgebra.reindex (preservesDPIndex k n d)
        (A.mulPieceRight (A.derivationPiece D x)
          (A.gamma.gammaPiece ((n : ℕ) - 1) d x))

namespace PreservesDP

variable {A : DividedPowerGradedAlgebra.{u, v} R}

/-- The square of a divided-power-compatible predifferential again preserves divided powers. -/
theorem square (d : Predifferential A.toChainGradedAlgebra)
    (h : A.PreservesDP d) :
    A.PreservesDP (ChainGradedAlgebra.Predifferential.square d) := sorry

end PreservesDP

/-- A predifferential on a divided-power graded algebra, with no square-zero assumption. -/
@[stacks 09PS "divided-power-compatible predifferential"]
structure Predifferential (A : DividedPowerGradedAlgebra.{u, v} R) where
  /-- The underlying degree-`-1` graded derivation. -/
  toPredifferential : ChainGradedAlgebra.Predifferential A.toChainGradedAlgebra
  /-- The predifferential preserves the divided powers. -/
  preservesDP : A.PreservesDP toPredifferential

namespace Predifferential

variable {A : DividedPowerGradedAlgebra.{u, v} R}

/-- A divided-power predifferential acts on homogeneous elements. -/
instance instCoeFun : CoeFun A.Predifferential (fun _ ↦ ∀ i : ℤ,
    A.toChainGradedAlgebra.X i → A.toChainGradedAlgebra.X (i - 1)) where
  coe d := d.toPredifferential

/-- Evaluation uses the underlying chain-graded predifferential. -/
@[simp]
theorem coe_apply (d : A.Predifferential) (i : ℤ)
    (x : A.toChainGradedAlgebra.X i) :
    d i x = d.toPredifferential i x := sorry

/-- A divided-power predifferential is square-zero exactly when its underlying predifferential
is square-zero. -/
def IsSquareZero (d : A.Predifferential) : Prop :=
  ChainGradedAlgebra.Predifferential.IsSquareZero d.toPredifferential

end Predifferential

/-- A closed divided-power-compatible derivation relative to a specified predifferential.
The reference predifferential need not itself preserve divided powers. -/
@[stacks 09PS "closed divided-power derivation on a graded algebra"]
structure DPDerivation (A : DividedPowerGradedAlgebra.{u, v} R)
    (d : ChainGradedAlgebra.Predifferential A.toChainGradedAlgebra) (k : ℤ) where
  /-- The underlying degree-`k` graded derivation. -/
  toDerivation : Derivation A.toChainGradedAlgebra k
  /-- The derivation is closed under the specified predifferential. -/
  isClosed : ChainGradedAlgebra.Derivation.IsClosed toDerivation d
  /-- The derivation preserves the divided powers. -/
  preservesDP : A.PreservesDP toDerivation

namespace DPDerivation

variable {A : DividedPowerGradedAlgebra.{u, v} R}
variable {d : ChainGradedAlgebra.Predifferential A.toChainGradedAlgebra} {k : ℤ}

/-- A divided-power derivation acts on homogeneous elements. -/
instance instCoeFun : CoeFun (A.DPDerivation d k) (fun _ ↦ ∀ i : ℤ,
    A.toChainGradedAlgebra.X i → A.toChainGradedAlgebra.X (i + k)) where
  coe D := D.toDerivation

/-- Evaluation uses the underlying graded derivation. -/
@[simp]
theorem coe_apply (D : A.DPDerivation d k) (i : ℤ)
    (x : A.toChainGradedAlgebra.X i) :
    D i x = D.toDerivation i x := sorry

/-- The underlying derivation determines a divided-power derivation. -/
theorem ext_toDerivation {D E : A.DPDerivation d k}
    (h : D.toDerivation = E.toDerivation) : D = E := by
  cases D
  cases E
  cases h
  rfl

/-- The square of a divided-power-compatible predifferential is a closed degree-`-2`
divided-power derivation. -/
@[stacks 09PS "square of a lifted divided-power predifferential"]
def square (d : A.Predifferential) : A.DPDerivation d.toPredifferential (-2) where
  toDerivation := ChainGradedAlgebra.Predifferential.square d.toPredifferential
  isClosed := ChainGradedAlgebra.Predifferential.square_isClosed d.toPredifferential
  preservesDP := PreservesDP.square d.toPredifferential d.preservesDP

/-- The square derivation evaluates as the square of the underlying predifferential. -/
@[simp]
theorem square_apply (d : A.Predifferential) (i : ℤ)
    (x : A.toChainGradedAlgebra.X i) :
    square d i x = ChainGradedAlgebra.Predifferential.square d.toPredifferential i x := sorry

end DPDerivation

end DividedPowerGradedAlgebra
