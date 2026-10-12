/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Spectrum.Prime.Constructible
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.29.4
@stack 00F8

The source adds finite presentation to Mathlib's canonical constructible-image
owner.  The witness construction is proof-stage work and is not chapter API.
-/

-- Lemma 10.29.4: every constructible subset of `Spec(R)` is the image of `Spec(S)` for some
-- finitely presented ring map `R → S`.
@[stacks 00F8]
#check @PrimeSpectrum.exists_finitePresentation_range_eq_of_isConstructible

@[stacks 00F8 "constructible image owner without finite presentation"]
#check @PrimeSpectrum.exists_range_eq_of_isConstructible
