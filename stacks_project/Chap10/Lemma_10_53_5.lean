/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Spectrum.Prime.Discrete
import StacksCheckRecall

@[expose] public section

universe u

section

variable {R : Type u} [CommRing R]
variable [Finite (MaximalSpectrum R)]
variable (hjac : (Ring.jacobson R).IsLocallyNilpotent)

/-!
Lemma 10.53.5 (1): a ring with finite maximal spectrum and locally
nilpotent Jacobson radical is the product of its localizations at maximal
ideals.

@stack 00JA
-/
@[stacks 00JA "(1)"]
#check ((MaximalSpectrum.Jacobson.toPiLocalizationEquiv hjac).toRingEquiv :
  R ≃+* MaximalSpectrum.PiLocalization R)

/- Lemma 10.53.5 (2): under the same hypotheses, every prime ideal is
maximal. -/
@[stacks 00JA "(2)"]
#check @PrimeSpectrum.Jacobson.isMaximal

#check (PrimeSpectrum.Jacobson.krullDimLE_zero hjac :
  Ring.KrullDimLE 0 R)

#check (MaximalSpectrum.Jacobson.toPiLocalizationEquiv_toAlgHom hjac :
  (MaximalSpectrum.Jacobson.toPiLocalizationEquiv hjac).toAlgHom =
    MaximalSpectrum.toPiLocalization R)

end
