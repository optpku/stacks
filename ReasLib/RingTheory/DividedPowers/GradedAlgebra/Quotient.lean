/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.ChainGradedAlgebra.Quotient
public import ReasLib.RingTheory.DividedPowers.GradedAlgebra.Predifferential

/-!
# Divided-power derivations on homogeneous base-ideal quotients

The divided powers of a graded algebra have canonical classes in every degreewise quotient by a
base ideal.  A derivation on that quotient is divided-power compatible when it satisfies the
usual formula on those classes.  This representative formula avoids selecting nonlinear quotient
operations before their well-definedness has been constructed, while still giving downstream
users the exact compatibility needed for deformation and obstruction theory.
-/

@[expose] public section

noncomputable section

universe u v

open ChainGradedAlgebra

namespace DividedPowerGradedAlgebra

variable {R : Type u} [CommRing R]

/-- The class of a homogeneous element in the degreewise quotient by a base ideal. -/
def quotientPiece (A : DividedPowerGradedAlgebra.{u, v} R) (I : Ideal R) (n : ℕ) :
    A.toGradedAlgebra.piece n →
      (A.toChainGradedAlgebra.quotientByIdeal I).X n :=
  fun x ↦ IdealQuotient.mk A.toChainGradedAlgebra I n x

/-- The homogeneous quotient class of a divided power. -/
def quotientGammaPiece (A : DividedPowerGradedAlgebra.{u, v} R) (I : Ideal R)
    (n d : ℕ) (x : A.toGradedAlgebra.piece (2 * (d + 1))) :
    (A.toChainGradedAlgebra.quotientByIdeal I).X (2 * (n * (d + 1)) : ℕ) :=
  A.quotientPiece I (2 * (n * (d + 1))) (A.gamma.gammaPiece n d x)

/-- The quotient class construction sends a divided power to `quotientGammaPiece`. -/
@[simp]
theorem quotientPiece_gamma (A : DividedPowerGradedAlgebra.{u, v} R) (I : Ideal R)
    (n d : ℕ) (x : A.toGradedAlgebra.piece (2 * (d + 1))) :
    A.quotientPiece I (2 * (n * (d + 1))) (A.gamma.gammaPiece n d x) =
      A.quotientGammaPiece I n d x := sorry

/-- A quotient derivation preserves divided powers when the usual divided-power derivation
formula holds on every homogeneous representative. -/
@[stacks 09PS "divided-power derivation formula modulo a base ideal"]
def PreservesDPModulo (A : DividedPowerGradedAlgebra.{u, v} R) (I : Ideal R)
    {k : ℤ} (D : Derivation (A.toChainGradedAlgebra.quotientByIdeal I) k) : Prop :=
  ∀ (n : ℕ+) (d : ℕ) (x : A.toGradedAlgebra.piece (2 * (d + 1))),
    D (2 * ((n : ℕ) * (d + 1)) : ℕ) (A.quotientGammaPiece I n d x) =
      (A.toChainGradedAlgebra.quotientByIdeal I).reindex (preservesDPIndex k n d)
        ((A.toChainGradedAlgebra.quotientByIdeal I).mul
          (((2 * (d + 1) : ℕ) : ℤ) + k)
          (2 * (((n : ℕ) - 1) * (d + 1)) : ℕ)
          (D (2 * (d + 1) : ℕ) (A.quotientPiece I (2 * (d + 1)) x))
          (A.quotientGammaPiece I ((n : ℕ) - 1) d x))

namespace IdealQuotient

/-- A closed divided-power-compatible derivation on the degreewise quotient by a base ideal. -/
@[stacks 09PS "divided-power derivation on a homogeneous base-ideal quotient"]
structure DPDerivation (A : DividedPowerGradedAlgebra.{u, v} R) (I : Ideal R)
    (d : ChainGradedAlgebra.Predifferential
      (A.toChainGradedAlgebra.quotientByIdeal I)) (k : ℤ) where
  /-- The underlying homogeneous quotient derivation. -/
  toDerivation : Derivation (A.toChainGradedAlgebra.quotientByIdeal I) k
  /-- The derivation is closed under the quotient predifferential. -/
  isClosed : Derivation.IsClosed toDerivation d
  /-- The derivation satisfies the divided-power formula on quotient classes. -/
  preservesDP : A.PreservesDPModulo I toDerivation

namespace DPDerivation

variable {A : DividedPowerGradedAlgebra.{u, v} R} {I : Ideal R}
variable {d : ChainGradedAlgebra.Predifferential
  (A.toChainGradedAlgebra.quotientByIdeal I)} {k : ℤ}

/-- A quotient divided-power derivation acts on homogeneous quotient elements. -/
instance instCoeFun : CoeFun (DPDerivation A I d k) (fun _ ↦ ∀ i : ℤ,
    (A.toChainGradedAlgebra.quotientByIdeal I).X i →
      (A.toChainGradedAlgebra.quotientByIdeal I).X (i + k)) where
  coe D := D.toDerivation

/-- Evaluation uses the underlying homogeneous quotient derivation. -/
@[simp]
theorem coe_apply (D : DPDerivation A I d k) (i : ℤ)
    (x : (A.toChainGradedAlgebra.quotientByIdeal I).X i) :
    D i x = D.toDerivation i x := sorry

/-- Quotient divided-power derivations are determined by their homogeneous values. -/
@[ext]
theorem ext {D E : DPDerivation A I d k}
    (h : ∀ i : ℤ, ∀ x : (A.toChainGradedAlgebra.quotientByIdeal I).X i,
      D i x = E i x) : D = E := sorry

/-- The defining laws of a quotient divided-power derivation. -/
theorem laws_spec (D : DPDerivation A I d k) :
    Derivation.IsClosed D.toDerivation d ∧
      A.PreservesDPModulo I D.toDerivation := sorry

end DPDerivation

end IdealQuotient

end DividedPowerGradedAlgebra
