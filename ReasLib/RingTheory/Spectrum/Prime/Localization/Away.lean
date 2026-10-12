/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Principal localizations on prime spectra

This leaf packages Mathlib's open embedding of the spectrum of a principal
localization as a homeomorphism onto the corresponding basic open.

@stack 00E4
-/

@[expose] public section

universe u

namespace PrimeSpectrum

/-- The spectrum of `R_f` is canonically homeomorphic to the basic open `D(f)` in `Spec(R)`. -/
@[stacks 00E4 "spectrum of a principal localization"]
noncomputable def localizationAwayHomeomorph
    {R : Type u} [CommRing R] (f : R) :
    PrimeSpectrum (Localization.Away f) ≃ₜ basicOpen f :=
  (localization_away_isOpenEmbedding (Localization.Away f) f).toHomeomorph.trans
    (Homeomorph.setCongr (localization_away_comap_range (Localization.Away f) f))

/-- The principal-localization homeomorphism is induced by comap along `R → R_f`. -/
@[simp]
theorem localizationAwayHomeomorph_apply
    {R : Type u} [CommRing R] (f : R) (p : PrimeSpectrum (Localization.Away f)) :
    (localizationAwayHomeomorph f p).1 =
      comap (algebraMap R (Localization.Away f)) p := rfl

/-- The inverse principal-localization homeomorphism extends a prime ideal along `R → R_f`. -/
theorem localizationAwayHomeomorph_symm_asIdeal
    {R : Type u} [CommRing R] (f : R) (p : basicOpen f) :
    ((localizationAwayHomeomorph f).symm p).asIdeal =
      p.1.asIdeal.map (algebraMap R (Localization.Away f)) := by
  let q := (localizationAwayHomeomorph f).symm p
  have hcomap : comap (algebraMap R (Localization.Away f)) q = p.1 := by
    rw [← localizationAwayHomeomorph_apply]
    exact congrArg Subtype.val ((localizationAwayHomeomorph f).apply_symm_apply p)
  rw [← hcomap, PrimeSpectrum.comap_asIdeal]
  exact (IsLocalization.map_under (Submonoid.powers f) (Localization.Away f) q.asIdeal).symm

end PrimeSpectrum
