/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.RingHom.Syntomic.Basic
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Conormal modules of syntomic presentations

@stack 07BT

For an explicit polynomial presentation whose localization is syntomic, the localized conormal
module is finite and projective.  The two properties are exposed independently.
-/

universe u

namespace RingHom.Syntomic

variable {R : Type u} [CommRing R]
variable {n : ℕ}

/-- Lemma 10.136.16, finiteness clause: the localized conormal module of a syntomic polynomial
presentation is finite. -/
@[stacks 07BT "finite localized conormal module"]
theorem idealCotangent_localizedAway_finite
    (I : Ideal (MvPolynomial (Fin n) R)) (g : MvPolynomial (Fin n) R ⧸ I)
    (hsyntomic : (algebraMap R (Localization.Away g)).Syntomic) :
    Module.Finite (Localization.Away g) (LocalizedModule.Away g I.Cotangent) := sorry

/-- Lemma 10.136.16, projectivity clause: the localized conormal module of a syntomic polynomial
presentation is projective. -/
@[stacks 07BT "projective localized conormal module"]
theorem idealCotangent_localizedAway_projective
    (I : Ideal (MvPolynomial (Fin n) R)) (g : MvPolynomial (Fin n) R ⧸ I)
    (hsyntomic : (algebraMap R (Localization.Away g)).Syntomic) :
    Module.Projective (Localization.Away g) (LocalizedModule.Away g I.Cotangent) := sorry

end RingHom.Syntomic
