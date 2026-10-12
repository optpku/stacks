/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Smooth.Factorization.Avoids

@[expose] public section

/-!
# Singular resolutions along target ideals

The reusable owner is indexed by an arbitrary target ideal.  A resolution at
a prime is the specialization to the underlying prime ideal; no point data is
needed to store the finite factorisation or its singular-ideal comparisons.
-/

universe u v w

namespace AlgHom

variable {R : Type u} {A : Type v} {Λ : Type w}
variable [CommRing R] [CommRing A] [CommRing Λ]
variable [Algebra R A] [Algebra R Λ]

namespace Factorisation.Finite

/-- A finite-presentation factorisation which enlarges the transported
singular ideal and whose new singular ideal avoids a prescribed target ideal. -/
@[stacks 07F7 "singular resolution along an ideal"]
structure Resolution (φ : A →ₐ[R] Λ) (J : Ideal Λ)
    extends AlgHom.Factorisation.Finite.Avoids φ J where
  /-- The original transported singular ideal is retained. -/
  singularIdeal_le :
    φ.singularIdealIn ≤ toAvoids.toTarget.singularIdealIn

namespace Resolution

variable {φ : A →ₐ[R] Λ} {J K : Ideal Λ}

/-- The finitely presented midpoint of a singular resolution. -/
abbrev mid (W : Resolution φ J) := W.toAvoids.mid

/-- The finite-presentation factorisation underlying a singular resolution. -/
abbrev factorisation (W : Resolution φ J) := W.toAvoids.base

/-- The source map of a singular resolution. -/
noncomputable abbrev fromSource (W : Resolution φ J) : A →ₐ[R] W.mid :=
  W.toAvoids.fromSource

/-- The target map of a singular resolution. -/
noncomputable abbrev toTarget (W : Resolution φ J) : W.mid →ₐ[R] Λ :=
  W.toAvoids.toTarget

/-- Attach the two singular-ideal comparisons to a finite factorisation. -/
def of (F : AlgHom.Factorisation.Finite φ)
    (singularIdeal_le : φ.singularIdealIn ≤ F.toTarget.singularIdealIn)
    (not_le : ¬ F.toTarget.singularIdealIn ≤ J) : Resolution φ J :=
  { toAvoids := Avoids.of F not_le
    singularIdeal_le := singularIdeal_le }

/-- Attach singular-resolution data to a categorical factorisation with a
finitely presented midpoint. -/
def ofFactorisation (F : φ.Factorisation)
    [Algebra.FinitePresentation R F.mid]
    (singularIdeal_le : φ.singularIdealIn ≤ F.toTarget.singularIdealIn)
    (not_le : ¬ F.toTarget.singularIdealIn ≤ J) : Resolution φ J :=
  of (Factorisation.Finite.of F) singularIdeal_le not_le

/-- Transport the singular-ideal comparison through a finite factorisation
built directly from its two maps. -/
theorem singularIdeal_le_ofMaps
    {B : Type (max u v w)} [CommRing B] [Algebra R B]
    [Algebra.FinitePresentation R B]
    (f : A →ₐ[R] B) (g : B →ₐ[R] Λ) (hcomp : g.comp f = φ)
    (hSing : φ.singularIdealIn ≤ g.singularIdealIn) :
    φ.singularIdealIn ≤
      (Factorisation.Finite.ofMaps f g hcomp).toTarget.singularIdealIn := sorry

/-- Transport target-ideal avoidance through a finite factorisation built
directly from its two maps. -/
theorem not_le_ofMaps
    {B : Type (max u v w)} [CommRing B] [Algebra R B]
    [Algebra.FinitePresentation R B]
    (f : A →ₐ[R] B) (g : B →ₐ[R] Λ) (hcomp : g.comp f = φ)
    (hnot : ¬ g.singularIdealIn ≤ J) :
    ¬ (Factorisation.Finite.ofMaps f g hcomp).toTarget.singularIdealIn ≤ J := sorry

/-- Build a singular resolution directly from its midpoint maps and the two
singular-ideal comparisons. -/
noncomputable def ofMaps
    {B : Type (max u v w)} [CommRing B] [Algebra R B]
    [Algebra.FinitePresentation R B]
    (f : A →ₐ[R] B) (g : B →ₐ[R] Λ) (hcomp : g.comp f = φ)
    (hSing : φ.singularIdealIn ≤ g.singularIdealIn)
    (hnot : ¬ g.singularIdealIn ≤ J) : Resolution φ J :=
  of (Factorisation.Finite.ofMaps f g hcomp)
    (singularIdeal_le_ofMaps f g hcomp hSing)
    (not_le_ofMaps f g hcomp hnot)

/-- Promote an avoiding factorisation once its singular ideal contains that
of the original map. -/
def ofAvoids (F : Avoids φ J)
    (singularIdeal_le : φ.singularIdealIn ≤ F.toTarget.singularIdealIn) :
    Resolution φ J :=
  { toAvoids := F
    singularIdeal_le := singularIdeal_le }

/-- The canonical source factorisation contains the transported singular ideal
of the original map. -/
theorem singularIdeal_le_initial [Algebra.FinitePresentation R A]
    (φ : A →ₐ[R] Λ) :
    φ.singularIdealIn ≤
      (Factorisation.Finite.initial φ).toTarget.singularIdealIn := sorry

/-- The canonical source factorisation avoids every ideal avoided by the
original transported singular ideal. -/
theorem not_le_initial [Algebra.FinitePresentation R A]
    (φ : A →ₐ[R] Λ) (J : Ideal Λ)
    (hnot : ¬ φ.singularIdealIn ≤ J) :
    ¬ (Factorisation.Finite.initial φ).toTarget.singularIdealIn ≤ J := sorry

/-- A finitely presented source gives a singular resolution along every ideal
avoided by the original transported singular ideal. -/
noncomputable def ofNotLe [Algebra.FinitePresentation R A]
    (φ : A →ₐ[R] Λ) (J : Ideal Λ)
    (hnot : ¬ φ.singularIdealIn ≤ J) : Resolution φ J :=
  of (Factorisation.Finite.initial φ) (singularIdeal_le_initial φ)
    (not_le_initial φ J hnot)

/-- Avoidance is contravariant in the prescribed target ideal. -/
theorem not_le_of_le (W : Resolution φ J) (hKJ : K ≤ J) :
    ¬ W.toTarget.singularIdealIn ≤ K := sorry

/-- Restrict a singular resolution to a smaller target ideal. -/
def ofLE (W : Resolution φ J) (hKJ : K ≤ J) : Resolution φ K :=
  of W.factorisation W.singularIdeal_le (W.not_le_of_le hKJ)

/-- The finite presentation, triangle law, and two singular-ideal comparisons
carried by a singular resolution. -/
@[stacks 07F7 "singular resolution specification"]
theorem spec (W : Resolution φ J) :
    Algebra.FinitePresentation R W.mid ∧
      W.toTarget.comp W.fromSource = φ ∧
      φ.singularIdealIn ≤ W.toTarget.singularIdealIn ∧
      ¬ W.toTarget.singularIdealIn ≤ J := sorry

end Resolution

end Factorisation.Finite

end AlgHom
