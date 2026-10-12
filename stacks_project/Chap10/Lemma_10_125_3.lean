/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.KrullDimension.Relative.Coordinate
import StacksCheckRecall

/-!
@stack 0520
-/

@[expose] public section

noncomputable section

open MvPolynomial
open RelativeDimensionAt

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FiniteType R S]
variable (q : PrimeSpectrum S) (n : ℕ)
variable (hdim : relativeDimensionAt R S q = (n : WithBot ℕ∞))
variable (r : ℕ)
variable (htr : Ideal.ResidueField.trdegToNat (q.asIdeal.under R) q.asIdeal = r)

/- Lemma 10.125.3: let `R → S` be a finite-type ring map and `q : Spec(S)`.
If `relativeDimensionAt R S q = n` and the residue-field transcendence degree is `r`,
then after inverting elements outside the relevant primes there is a quasi-finite
polynomial chart whose contraction is the base prime together with the tail coordinate ideal. -/
@[stacks 0520]
#check (RelativeDimensionAt.exists_quasiFinite_localized_comap_eq_tailIdeal_of_trdeg
    (R := R) (S := S) q n hdim r htr :
    ∃ f : R, f ∉ q.asIdeal.under R ∧
      ∃ g : S, g ∉ q.asIdeal ∧
        ∃ φ : MvPolynomial (Fin n) (Localization.Away f) →+*
            Localization.Away g,
          φ.QuasiFinite ∧
            Ideal.comap φ
                (Ideal.map (algebraMap S (Localization.Away g)) q.asIdeal) =
              Ideal.map
                  (algebraMap R (MvPolynomial (Fin n) (Localization.Away f)))
                (q.asIdeal.under R) ⊔
                MvPolynomial.NoetherNormalization.tailIdeal (Localization.Away f) n r)

/- The canonical-index convenience theorem removes `r` and `htr` when the target index is derived. -/
@[stacks 0520]
#check (RelativeDimensionAt.exists_quasiFinite_localized_comap_eq_tailIdeal
    (R := R) (S := S) q n hdim :
    ∃ f : R, f ∉ q.asIdeal.under R ∧
      ∃ g : S, g ∉ q.asIdeal ∧
        ∃ φ : MvPolynomial (Fin n) (Localization.Away f) →+*
            Localization.Away g,
          φ.QuasiFinite ∧
            Ideal.comap φ
                (Ideal.map (algebraMap S (Localization.Away g)) q.asIdeal) =
              Ideal.map
                  (algebraMap R (MvPolynomial (Fin n) (Localization.Away f)))
                (q.asIdeal.under R) ⊔
                MvPolynomial.NoetherNormalization.tailIdeal (Localization.Away f) n
                  (Ideal.ResidueField.trdegToNat (q.asIdeal.under R) q.asIdeal))

#check @RelativeDimensionAt.exists_quasiFinite_localized_comap_eq_tailIdeal

end
