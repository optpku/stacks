module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import ReasLib.AlgebraicGeometry.PuncturedSpectrum
public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.Purity
public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale
public import ReasLib.RingTheory.Depth

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped ENat

universe u

namespace AlgebraicGeometry.Scheme

/-- For a Noetherian local ring `A` of depth at least two and a positive number `d`
of power-series variables, finite étale base change from an open of
`Spec (MvPowerSeries (Fin d) A)` to its constant-coefficient closed fiber is fully
faithful when that fiber is the punctured spectrum of `A`. -/
theorem finiteEtaleBaseChange_fullyFaithful_of_powerSeriesDepth
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hdepth : (2 : ℕ∞) ≤ moduleDepth A A) {d : ℕ} (hd : 0 < d)
    (V : (Spec (CommRingCat.of (MvPowerSeries (Fin d) A))).Opens)
    (hV :
      let i := Spec.map (CommRingCat.ofHom
        (MvPowerSeries.constantCoeff : MvPowerSeries (Fin d) A →+* A))
      i ⁻¹ᵁ V = PuncturedSpectrum.puncturedOpen A) :
    let i := Spec.map (CommRingCat.ofHom
      (MvPowerSeries.constantCoeff : MvPowerSeries (Fin d) A →+* A))
    Nonempty (finiteEtaleBaseChange (pullback.fst V.ι i)).FullyFaithful := sorry

/-- For a Noetherian local ring `A` of depth at least two and a positive number `d`
of power-series variables, restriction of finite étale covers of
`Spec (MvPowerSeries (Fin d) A)` to an open is an equivalence when the open contains
every prime whose contraction is not the maximal ideal of `A` and the prime
obtained by extending that maximal ideal. -/
theorem finiteEtaleBaseChange_isEquivalence_of_powerSeriesDepth
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hdepth : (2 : ℕ∞) ≤ moduleDepth A A) {d : ℕ} (hd : 0 < d)
    (V : (Spec (CommRingCat.of (MvPowerSeries (Fin d) A))).Opens)
    (hV : ∀ q : PrimeSpectrum (MvPowerSeries (Fin d) A),
      Ideal.comap (algebraMap A (MvPowerSeries (Fin d) A)) q.asIdeal ≠
          IsLocalRing.maximalIdeal A ∨
        q.asIdeal =
          Ideal.map (algebraMap A (MvPowerSeries (Fin d) A))
            (IsLocalRing.maximalIdeal A) →
      q ∈ V) :
    Functor.IsEquivalence (finiteEtaleBaseChange V.ι) := sorry

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.PuncturedSpectrum

/-- Multivariate power series in a positive finite number of variables over a
Noetherian local ring of depth at least two satisfy purity. -/
theorem hasPurity_mvPowerSeries
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hdepth : (2 : ℕ∞) ≤ moduleDepth A A) {d : ℕ} (hd : 0 < d) :
    HasPurity (MvPowerSeries (Fin d) A) := sorry

end AlgebraicGeometry.PuncturedSpectrum
