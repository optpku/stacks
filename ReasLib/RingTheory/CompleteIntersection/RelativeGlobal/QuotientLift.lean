/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.CompleteIntersection.RelativeGlobal.Basic
public import ReasLib.RingTheory.RingHom.Syntomic.Cover

@[expose] public section

/-!
# Lifting Relative Global Complete Intersections Across Quotients

@stack 00T0

This leaf separates the algebra-level lifting of a relative global complete
intersection from the syntomic principal-open cover that uses it.
-/

universe u v

namespace Algebra

namespace IsRelativeGlobalCompleteIntersection

variable {R : Type u} {T : Type v} [CommRing R] {I : Ideal R}
variable [CommRing T] [Algebra (R ⧸ I) T]

/-- A relative global complete intersection over a quotient ring is the
reduction of one over the original ring. -/
theorem exists_lift_of_quotient (hT : IsRelativeGlobalCompleteIntersection (R ⧸ I) T) :
    ∃ (S : Type (max u v)) (_ : CommRing S) (_ : Algebra R S)
      (_ : IsRelativeGlobalCompleteIntersection R S),
        Nonempty (T ≃ₐ[R ⧸ I] (S ⧸ Ideal.map (algebraMap R S) I)) := sorry

end IsRelativeGlobalCompleteIntersection

namespace Syntomic

variable {R : Type u} {Sbar : Type v} [CommRing R] {I : Ideal R}
variable [CommRing Sbar] [Algebra (R ⧸ I) Sbar]

/-- A syntomic algebra over `R ⧸ I` admits a finite principal-open cover whose
members lift to relative global complete intersections over `R`. -/
theorem exists_relativeGlobalCompleteIntersectionLiftStandardOpenCover_of_quotient
    (hSbar : (algebraMap (R ⧸ I) Sbar).Syntomic) :
    ∃ U : PrimeSpectrum.StandardOpenCover (R := Sbar),
      ∀ i : U.index, ∃ (S : Type (max u v)) (_ : CommRing S) (_ : Algebra R S)
        (_ : IsRelativeGlobalCompleteIntersection R S),
          Nonempty ((Localization.Away (U.generator i)) ≃ₐ[R ⧸ I]
            (S ⧸ Ideal.map (algebraMap R S) I)) := sorry

/-- Lemma 10.136.18, tag `00T0`: a syntomic algebra over `R ⧸ I` admits a
unit-ideal cover by basic opens that are reductions of relative global
complete intersections over `R`. -/
@[stacks 00T0 "relative global complete intersection lift cover of a syntomic quotient algebra"]
theorem exists_relativeGlobalCompleteIntersectionLiftCover_of_quotient
    (hSbar : (algebraMap (R ⧸ I) Sbar).Syntomic) :
    ∃ s : Set Sbar, Ideal.span s = ⊤ ∧
      ∀ g ∈ s, ∃ (S : Type (max u v)) (_ : CommRing S) (_ : Algebra R S)
        (_ : IsRelativeGlobalCompleteIntersection R S),
          Nonempty ((Localization.Away g) ≃ₐ[R ⧸ I]
            (S ⧸ Ideal.map (algebraMap R S) I)) := sorry

end Syntomic

end Algebra
