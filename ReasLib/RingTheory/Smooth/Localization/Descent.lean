/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.AlgHom.Factorisation
public import ReasLib.RingTheory.Localization.BaseChange
public import ReasLib.RingTheory.Smooth.Standard.Element.Selected
import Mathlib.Tactic.CrossRefAttribute

/-!
# Descent of localized smooth factorizations

This leaf owns the finite-presentation descent statement for a localized smooth
factorization.  The map `φ` is explicit; a scalar-tower structural map is only
a specialization of this interface.
-/

@[expose] public section

universe u v w

namespace AlgHom.Localization

variable {R : Type u} {A : Type v} {Λ : Type w}
variable [CommRing R] [CommRing A] [CommRing Λ]
variable [Algebra R A] [Algebra R Λ]

/-- A finite-presentation descent of a localized factorisation, together with
a denominator at which its midpoint is elementary standard. -/
@[stacks 07F4 "localized factorisation descent"]
structure Descent (φ : A →ₐ[R] Λ) (S : Submonoid R) where
  /-- The descended finite-presentation factorisation. -/
  factorisation : AlgHom.Factorisation.Finite φ
  /-- A denominator witnessing the elementary-standard locus. -/
  denominator : S
  /-- The chosen denominator is elementary standard in the midpoint. -/
  elementaryStandard :
    Algebra.IsElementaryStandard R
      (algebraMap R factorisation.mid denominator)

namespace Descent

variable {φ : A →ₐ[R] Λ} {S : Submonoid R}

/-- The finitely presented midpoint of a localization descent. -/
abbrev mid (D : Descent φ S) := D.factorisation.mid

/-- The source map of a localization descent. -/
noncomputable abbrev fromSource (D : Descent φ S) : A →ₐ[R] D.mid :=
  D.factorisation.fromSource

/-- The target map of a localization descent. -/
noncomputable abbrev toTarget (D : Descent φ S) : D.mid →ₐ[R] Λ :=
  D.factorisation.toTarget

/-- The maps carried by a localization descent factor the original map. -/
theorem factor (D : Descent φ S) :
    D.toTarget.comp D.fromSource = φ := sorry

/-- Build localization-descent data from a finite factorisation and a
denominator in its elementary-standard locus. -/
def of (F : AlgHom.Factorisation.Finite φ) (s : S)
    (elementaryStandard :
      Algebra.IsElementaryStandard R (algebraMap R F.mid s)) :
    Descent φ S :=
  { factorisation := F
    denominator := s
    elementaryStandard := elementaryStandard }

/-- The finite-presentation, triangle, and elementary-standard properties
carried by a localization descent. -/
@[stacks 07F4 "localized factorisation descent specification"]
theorem spec (D : Descent φ S) :
    Algebra.FinitePresentation R D.mid ∧
      D.toTarget.comp D.fromSource = φ ∧
      Algebra.IsElementaryStandard R
        (algebraMap R D.mid D.denominator) := sorry

/-- Lemma 16.8.3 (tag `07F4`): a factorization of the localization of an
`R`-algebra map through a smooth localized algebra descends to a factorization
over `R` in which an element of the chosen denominator submonoid is elementary
standard. -/
@[stacks 07F4]
theorem nonempty
    (φ : A →ₐ[R] Λ) (S : Submonoid R) [Algebra.FinitePresentation R A]
    (F : AlgHom.Factorisation.Smooth (baseChange φ S)) :
    Nonempty (Descent φ S) := sorry

end Descent

end AlgHom.Localization
