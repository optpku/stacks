/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Spectrum.Prime.BeauvilleLaszlo
import StacksCheckRecall

/-!
# Lemma 15.91.3

The base-change and away-localization branches jointly cover the source
prime spectrum.  The disjoint union in the source is represented by `Sum`.

@stack 0BNM
-/

@[expose] public section

universe u v

namespace Lemma_15_91_3

open PrimeSpectrum.BeauvilleLaszlo

variable {R : Type u} [CommRing R]
variable {R' : Type v} [CommRing R']
variable (φ : R →+* R') (f : R)

/- The displayed map has the source's two spectrum branches. -/
@[stacks 0BNM "the Beauville-Laszlo prime-spectrum cover map"]
#check (coverMap φ f :
  PrimeSpectrum R' ⊕ PrimeSpectrum (Localization.Away f) →
    PrimeSpectrum R)

variable (hquot :
  Function.Bijective (principalIdealQuotientMap φ f rfl))

/- Lemma 15.91.3 (0BNM): if `R / fR ⟶ R' / fR'` is bijective, the
displayed map from the two spectra is surjective. -/
@[stacks 0BNM "surjectivity of the Beauville-Laszlo prime-spectrum cover"]
#check (coverMap_surjective_of_principalQuotientMap_bijective
  φ f hquot : Function.Surjective (coverMap φ f))

/- The principal-adic completion supplies the required quotient comparison. -/
@[stacks 0BNM "principal-adic prime-spectrum cover"]
#check (coverMap_principalAdicCompletion_surjective f :
  Function.Surjective
    (coverMap (algebraMap R (principalAdicCompletion f)) f))

end Lemma_15_91_3
