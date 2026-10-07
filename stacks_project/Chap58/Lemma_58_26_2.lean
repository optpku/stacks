module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.PowerSeries
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped ENat

universe u

namespace AlgebraicGeometry.Scheme

/- Lemma 58.26.2 (1): if `(A, m)` is a Noetherian local ring of depth at least `2` and
`B = A[[x₁, …, x_d]]` with `d ≥ 1`, then for any open `V ⊂ Y = Spec B` containing every
prime `q ⊂ B` with `q ∩ A ≠ m` and also containing the prime `m B`, restriction
`FÉt_Y ⥤ FÉt_V` is an equivalence. -/
@[stacks 0EYA] #check
  (AlgebraicGeometry.Scheme.finiteEtaleBaseChange_isEquivalence_of_powerSeriesDepth :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hdepth : (2 : ℕ∞) ≤ moduleDepth A A) {d : ℕ} (hd : 0 < d)
    (V : (Spec (CommRingCat.of (MvPowerSeries (Fin d) A))).Opens)
    (hV : ∀ q : PrimeSpectrum (MvPowerSeries (Fin d) A),
      Ideal.comap (algebraMap A (MvPowerSeries (Fin d) A)) q.asIdeal ≠
          IsLocalRing.maximalIdeal A ∨
        q.asIdeal =
          Ideal.map (algebraMap A (MvPowerSeries (Fin d) A))
            (IsLocalRing.maximalIdeal A) →
      q ∈ V),
    Functor.IsEquivalence (finiteEtaleBaseChange V.ι))

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.PuncturedSpectrum

/- Lemma 58.26.2 (2): under the same hypotheses, purity holds for
`B = A[[x₁, …, x_d]]`. -/
@[stacks 0EYA] #check
  (AlgebraicGeometry.PuncturedSpectrum.hasPurity_mvPowerSeries :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hdepth : (2 : ℕ∞) ≤ moduleDepth A A) {d : ℕ} (hd : 0 < d),
    HasPurity (MvPowerSeries (Fin d) A))

end AlgebraicGeometry.PuncturedSpectrum
