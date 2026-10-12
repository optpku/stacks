/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DividedPowers.Envelope.Universal
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 60.2.1: for a divided-power ring `(A, I, γ)`, a ring map `f : A →+* B`,
and an ideal `J` containing `Ideal.map f I`, there exists a divided-power envelope
with the universal unique-lifting property for maps of ring-ideal pairs. -/
@[stacks 07H8] #check (@DividedPowerEnvelope.existsUniversal :
  ∀ {A B : Type u} [CommRing A] [CommRing B]
    {I : Ideal A} (γ : DividedPowers I) (f : A →+* B) (J : Ideal B)
    (hIJ : Ideal.map f I ≤ J),
    ∃ E : DividedPowerEnvelope I γ f J hIJ,
      DividedPowerEnvelope.IsUniversal γ f hIJ E)
