/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Localization.AsSubring
public import ReasLib.RingTheory.CohenMacaulay.SerreCondition
public import ReasLib.RingTheory.KrullDimension.HeightOne
import Mathlib.Tactic.CrossRefAttribute

/-!
# Height-one localizations inside a fraction field

The ambient field is an arbitrary fraction-field model.  The intersection is expressed in the
lattice of `R`-subalgebras, where `⊥` is exactly the image of `R`.

@stack 031T
-/

@[expose] public section

noncomputable section

universe u v

namespace PrimeSpectrum.HeightOne

variable {R : Type u} [CommRing R] [IsDomain R]

/-- The localization at a height-one prime, realized as an `R`-subalgebra of a chosen fraction
field. -/
@[stacks 031T "height-one localization in a fraction field"]
abbrev localizationSubalgebra
    (p : PrimeSpectrum.HeightOne R) (K : Type v)
    [Field K] [Algebra R K] [IsFractionRing R K] : Subalgebra R K :=
  Localization.subalgebra.ofField K p.asIdeal.primeCompl
    p.asIdeal.primeCompl_le_nonZeroDivisors

/-- An `(S₂)` domain is the intersection of its height-one localizations in any chosen fraction
field. -/
@[stacks 031T "intersection of height-one localizations"]
theorem iInf_localization_eq_bot
    [R ⊧ (S₂)] (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K] :
    (⨅ p : PrimeSpectrum.HeightOne R, p.localizationSubalgebra K) = ⊥ := sorry

end PrimeSpectrum.HeightOne
