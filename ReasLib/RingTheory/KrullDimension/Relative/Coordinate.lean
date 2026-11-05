/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.RingHom.QuasiFinite
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.KrullDimension.Relative.QuasiFinite
public import ReasLib.RingTheory.LocalRing.ResidueField.Transcendence
public import ReasLib.RingTheory.MvPolynomial.NoetherNormalization.Prime

@[expose] public section

/-!
# Coordinate-normalized quasi-finite charts

This leaf owns the reusable source-facing conclusion of the relative Noether
normalization step.  The residue-field transcendence index is expressed through
`Ideal.ResidueField.trdegToNat`, which selects the canonical lying-over algebra
without forcing a competing ambient `Algebra` instance.
-/

open MvPolynomial

universe u v

namespace RelativeDimensionAt

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Lemma 10.125.3, tag 0520: at a point of relative dimension `n` whose residue-field
transcendence degree over the contracted prime is `r`, a finite-type algebra admits localized
polynomial coordinates whose quasi-finite `R`-algebra map contracts the target prime to the base prime
together with the tail coordinate ideal. -/
@[stacks 0520]
theorem exists_quasiFinite_localized_comap_eq_tailIdeal_of_trdeg
    [Algebra.FiniteType R S] (q : PrimeSpectrum S) (n : ℕ)
    (hdim : relativeDimensionAt R S q = (n : WithBot ℕ∞)) (r : ℕ)
    (htr : Ideal.ResidueField.trdegToNat (q.asIdeal.under R) q.asIdeal = r) :
    ∃ f : R, f ∉ q.asIdeal.under R ∧
      ∃ g : S, g ∉ q.asIdeal ∧
        ∃ φ : MvPolynomial (Fin n) (Localization.Away f) →ₐ[R]
            Localization.Away g,
          φ.toRingHom.QuasiFinite ∧
            Ideal.comap φ.toRingHom
                (Ideal.map (algebraMap S (Localization.Away g)) q.asIdeal) =
              Ideal.map
                  (algebraMap R (MvPolynomial (Fin n) (Localization.Away f)))
                (q.asIdeal.under R) ⊔
                MvPolynomial.NoetherNormalization.tailIdeal (Localization.Away f) n
                  r := sorry
/- Proof strategy: apply the quasi-finite polynomial localization owner, then
apply finite-variable Noether normalization over the residue field and spread
the resulting coordinate map across the two localizations. -/

/-- The canonical-index specialization of 0520, obtained by taking `r` to be the residue-field
transcendence degree of the target prime over its contracted prime. -/
@[stacks 0520 "canonical transcendence-degree index for 0520"]
theorem exists_quasiFinite_localized_comap_eq_tailIdeal
    [Algebra.FiniteType R S] (q : PrimeSpectrum S) (n : ℕ)
    (hdim : relativeDimensionAt R S q = (n : WithBot ℕ∞)) :
    ∃ f : R, f ∉ q.asIdeal.under R ∧
      ∃ g : S, g ∉ q.asIdeal ∧
        ∃ φ : MvPolynomial (Fin n) (Localization.Away f) →ₐ[R]
            Localization.Away g,
          φ.toRingHom.QuasiFinite ∧
            Ideal.comap φ.toRingHom
                (Ideal.map (algebraMap S (Localization.Away g)) q.asIdeal) =
              Ideal.map
                  (algebraMap R (MvPolynomial (Fin n) (Localization.Away f)))
                (q.asIdeal.under R) ⊔
                MvPolynomial.NoetherNormalization.tailIdeal (Localization.Away f) n
                  (Ideal.ResidueField.trdegToNat (q.asIdeal.under R) q.asIdeal) := by
  exact exists_quasiFinite_localized_comap_eq_tailIdeal_of_trdeg q n hdim _ rfl

end RelativeDimensionAt
