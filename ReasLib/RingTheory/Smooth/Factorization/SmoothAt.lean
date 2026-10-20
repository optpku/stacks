/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Smooth.Factorization.Avoids

@[expose] public section

/-!
# Finite factorizations smooth at a target prime

Primewise smoothness is the bundled-point specialization of ideal avoidance.
The conversion from avoidance lives here so the generic avoidance leaf does
not depend on prime-specific API.
-/

universe u v w

namespace AlgHom.Factorisation.Finite

variable {R : Type u} {A : Type v} {Λ : Type w}
variable [CommRing R] [CommRing A] [CommRing Λ]
variable [Algebra R A] [Algebra R Λ]

/-- A finite-presentation factorisation whose midpoint is smooth at the
prime pulled back from the target. -/
@[stacks 07F9 "finite factorisation smooth at a target prime"]
structure SmoothAt (φ : A →ₐ[R] Λ) (q : PrimeSpectrum Λ) where
  /-- The underlying finite-presentation factorisation. -/
  base : AlgHom.Factorisation.Finite φ
  /-- Smoothness of the midpoint at the prime under the target point. -/
  smoothAt : Algebra.SmoothAtPrime R base.mid
    (PrimeSpectrum.comap base.toTarget.toRingHom q)

namespace SmoothAt

variable {φ : A →ₐ[R] Λ} {q : PrimeSpectrum Λ}

/-- The finitely presented midpoint of a pointwise-smooth factorisation. -/
abbrev mid (F : SmoothAt φ q) := F.base.mid

/-- The source map of a pointwise-smooth factorisation. -/
noncomputable abbrev fromSource (F : SmoothAt φ q) : A →ₐ[R] F.mid :=
  F.base.fromSource

/-- The target map of a pointwise-smooth factorisation. -/
noncomputable abbrev toTarget (F : SmoothAt φ q) : F.mid →ₐ[R] Λ :=
  F.base.toTarget

/-- Attach pointwise smoothness to a finite-presentation factorisation. -/
def of (F : AlgHom.Factorisation.Finite φ)
    (smoothAt : Algebra.SmoothAtPrime R F.mid
      (PrimeSpectrum.comap F.toTarget.toRingHom q)) : SmoothAt φ q :=
  { base := F
    smoothAt := smoothAt }

/-- The transported singular ideal of a pointwise-smooth factorisation
avoids the target prime. -/
theorem not_le (F : SmoothAt φ q) :
    ¬ F.toTarget.singularIdealIn ≤ q.asIdeal := sorry

/-- Forget pointwise smoothness to the equivalent singular-ideal avoidance
view at the target prime. -/
def toAvoids (F : SmoothAt φ q) : Avoids φ q.asIdeal :=
  Avoids.of F.base F.not_le

/-- The finite presentation, triangle law, and pointwise smoothness carried
by a pointwise-smooth factorisation. -/
theorem spec (F : SmoothAt φ q) :
    Algebra.FinitePresentation R F.mid ∧
      F.toTarget.comp F.fromSource = φ ∧
      Algebra.SmoothAtPrime R F.mid
        (PrimeSpectrum.comap F.toTarget.toRingHom q) := sorry

end SmoothAt

namespace Avoids

variable {φ : A →ₐ[R] Λ} {q : PrimeSpectrum Λ}

/-- Avoiding a target prime is equivalent to smoothness of the midpoint at
the pulled-back prime. -/
theorem smoothAt (F : Avoids φ q.asIdeal) :
    Algebra.SmoothAtPrime R F.mid
      (PrimeSpectrum.comap F.toTarget.toRingHom q) := sorry

/-- Reinterpret avoidance of a target prime as a pointwise-smooth
factorisation. -/
def toSmoothAt (F : Avoids φ q.asIdeal) : SmoothAt φ q :=
  SmoothAt.of F.base F.smoothAt

end Avoids

end AlgHom.Factorisation.Finite
