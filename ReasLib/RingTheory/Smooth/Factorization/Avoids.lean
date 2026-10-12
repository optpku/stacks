/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.AlgHom.Factorisation
public import ReasLib.RingTheory.Smooth.SingularLocus

@[expose] public section

/-!
# Finite factorizations avoiding an ideal

This leaf attaches an ideal-avoidance condition to the generic finite
factorization owner.  It is independent of prime-specific topology.
-/

universe u v w

namespace AlgHom.Factorisation.Finite

variable {R : Type u} {A : Type v} {Λ : Type w}
variable [CommRing R] [CommRing A] [CommRing Λ]
variable [Algebra R A] [Algebra R Λ]

/-- A finite-presentation factorisation whose transported singular ideal
avoids a prescribed target ideal. -/
@[stacks 07F9 "finite factorisation avoiding an ideal"]
structure Avoids (φ : A →ₐ[R] Λ) (J : Ideal Λ) where
  /-- The underlying finite-presentation factorisation. -/
  base : AlgHom.Factorisation.Finite φ
  /-- The transported singular ideal is not contained in the prescribed ideal. -/
  not_le : ¬ base.toTarget.singularIdealIn ≤ J

namespace Avoids

variable {φ : A →ₐ[R] Λ} {J : Ideal Λ}

/-- The finitely presented midpoint of an avoiding factorisation. -/
abbrev mid (F : Avoids φ J) := F.base.mid

/-- The source map of an avoiding factorisation. -/
noncomputable abbrev fromSource (F : Avoids φ J) : A →ₐ[R] F.mid :=
  F.base.fromSource

/-- The target map of an avoiding factorisation. -/
noncomputable abbrev toTarget (F : Avoids φ J) : F.mid →ₐ[R] Λ :=
  F.base.toTarget

/-- Attach an avoidance condition to a finite-presentation factorisation. -/
def of (F : AlgHom.Factorisation.Finite φ)
    (not_le : ¬ F.toTarget.singularIdealIn ≤ J) : Avoids φ J :=
  { base := F
    not_le := not_le }

/-- The finite presentation, triangle law, and avoidance condition carried
by an avoiding factorisation. -/
theorem spec (F : Avoids φ J) :
    Algebra.FinitePresentation R F.mid ∧
      F.toTarget.comp F.fromSource = φ ∧
      ¬ F.toTarget.singularIdealIn ≤ J := sorry

end Avoids

end AlgHom.Factorisation.Finite
