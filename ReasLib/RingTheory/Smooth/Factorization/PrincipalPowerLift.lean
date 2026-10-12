/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.RingTheory.RingHom.Smooth
public import ReasLib.Algebra.AlgHom.Factorisation
public import ReasLib.RingTheory.Algebra.Quotient.PrincipalPower
public import ReasLib.RingTheory.Smooth.SingularLocus

@[expose] public section

/-!
# Lifting finite factorizations across a principal-power quotient

This leaf records localization smoothness and reduced singular-ideal control
without importing primewise factorization API.
-/

universe u v w x

namespace AlgHom.Factorisation.Finite

variable {R : Type u} {A : Type v} {Λ : Type w} {C : Type x}
variable [CommRing R] [CommRing A] [CommRing Λ] [CommRing C]
variable [Algebra R A] [Algebra R Λ]

/-- A finite factorisation of an algebra map which is smooth after inverting
`π` and whose transported singular ideal is controlled by a factorisation of
the reduction modulo `π ^ n`. -/
@[stacks 07F0 "principal-power lift of a finite factorisation"]
structure PrincipalPowerLift (π : R) (n : ℕ) (φ : A →ₐ[R] Λ)
    [Algebra (R ⧸ principalPowerIdeal π n) C]
    (toReduction : C →ₐ[R ⧸ principalPowerIdeal π n]
      Algebra.PrincipalQuotient R Λ π n) where
  /-- The underlying finite-presentation factorisation over the original base. -/
  base : AlgHom.Factorisation.Finite φ
  /-- The midpoint becomes smooth after inverting the principal parameter. -/
  smoothAway : (Localization.awayMap (algebraMap R base.mid) π).Smooth
  /-- The singular ideal of the reduced intermediate algebra maps into the
  reduced transported singular ideal of the target map. -/
  singularIdeal_le :
    Ideal.map toReduction.toRingHom
        (Algebra.singularIdeal (R ⧸ principalPowerIdeal π n) C) ≤
      Ideal.map (Algebra.PrincipalQuotient.mk (A := Λ) π n).toRingHom
        base.toTarget.singularIdealIn

namespace PrincipalPowerLift

variable {π : R} {n : ℕ} {φ : A →ₐ[R] Λ}
variable [Algebra (R ⧸ principalPowerIdeal π n) C]
variable {toReduction : C →ₐ[R ⧸ principalPowerIdeal π n]
  Algebra.PrincipalQuotient R Λ π n}

/-- The midpoint of a principal-power lift. -/
abbrev mid (F : PrincipalPowerLift π n φ toReduction) := F.base.mid

/-- The map from the original source to a principal-power lift. -/
noncomputable abbrev fromSource (F : PrincipalPowerLift π n φ toReduction) :
    A →ₐ[R] F.mid := F.base.fromSource

/-- The map from a principal-power lift to the original target. -/
noncomputable abbrev toTarget (F : PrincipalPowerLift π n φ toReduction) :
    F.mid →ₐ[R] Λ := F.base.toTarget

/-- The maps carried by a principal-power lift factor the original map. -/
theorem factor (F : PrincipalPowerLift π n φ toReduction) :
    F.toTarget.comp F.fromSource = φ := sorry

/-- Attach localization smoothness and reduced singular-ideal control to a
finite factorisation. -/
def of (F : AlgHom.Factorisation.Finite φ)
    (smoothAway : (Localization.awayMap (algebraMap R F.mid) π).Smooth)
    (singularIdeal_le :
      Ideal.map toReduction.toRingHom
          (Algebra.singularIdeal (R ⧸ principalPowerIdeal π n) C) ≤
        Ideal.map (Algebra.PrincipalQuotient.mk (A := Λ) π n).toRingHom
          F.toTarget.singularIdealIn) :
    PrincipalPowerLift π n φ toReduction :=
  { base := F
    smoothAway := smoothAway
    singularIdeal_le := singularIdeal_le }

/-- The finite-presentation, triangle, localization, and reduced
singular-control properties carried by a principal-power lift. -/
theorem spec (F : PrincipalPowerLift π n φ toReduction) :
    Algebra.FinitePresentation R F.mid ∧
      F.toTarget.comp F.fromSource = φ ∧
      (Localization.awayMap (algebraMap R F.mid) π).Smooth ∧
      Ideal.map toReduction.toRingHom
          (Algebra.singularIdeal (R ⧸ principalPowerIdeal π n) C) ≤
        Ideal.map (Algebra.PrincipalQuotient.mk (A := Λ) π n).toRingHom
          F.toTarget.singularIdealIn := sorry

end PrincipalPowerLift

end AlgHom.Factorisation.Finite
