/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import ReasLib.RingTheory.AdicCompletion.Principal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Prime-spectrum covers for Beauville-Laszlo pairs

A base change agreeing modulo `f`, together with localization away from `f`,
covers the prime spectrum of the source.

@stack 0BNM
-/

@[expose] public section

universe u v

namespace PrimeSpectrum.BeauvilleLaszlo

variable {R : Type u} [CommRing R]
variable {R' : Type v} [CommRing R']

/-- The map from the disjoint union `Spec(R') ⊔ Spec(R_f)` to `Spec(R)`
induced by a ring map `R ⟶ R'` and the away localization. -/
@[stacks 0BNM "the Beauville-Laszlo prime-spectrum cover map"]
def coverMap (φ : R →+* R') (f : R) :
    PrimeSpectrum R' ⊕ PrimeSpectrum (Localization.Away f) →
      PrimeSpectrum R :=
  Sum.elim (PrimeSpectrum.comap φ)
    (PrimeSpectrum.comap (algebraMap R (Localization.Away f)))

/-- If `R / fR ⟶ R' / fR'` is bijective, the two branches of the
Beauville-Laszlo prime-spectrum cover map are jointly surjective. -/
@[stacks 0BNM "surjectivity of the Beauville-Laszlo prime-spectrum cover"]
theorem coverMap_surjective_of_principalQuotientMap_bijective
    (φ : R →+* R') (f : R)
    (hquot : Function.Bijective (principalIdealQuotientMap φ f rfl)) :
    Function.Surjective (coverMap φ f) := sorry

/-- The principal-adic completion and the away localization jointly cover
the prime spectrum of the source ring. -/
@[stacks 0BNM "principal-adic prime-spectrum cover"]
theorem coverMap_principalAdicCompletion_surjective (f : R) :
    Function.Surjective
      (coverMap (algebraMap R (principalAdicCompletion f)) f) := sorry

end PrimeSpectrum.BeauvilleLaszlo
