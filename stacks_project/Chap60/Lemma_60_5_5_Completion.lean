/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DividedPowers.Envelope.Completion

@[expose] public section

universe u

namespace DividedPowers.PAdic

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (A P : Type u) [CommRing A] [CommRing P]
variable (I : Ideal A) (γ : DividedPowers I)
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable [Algebra A P]
variable (J : Ideal P) (hIJ : Ideal.map (algebraMap A P) I ≤ J)
variable (E : DividedPowerEnvelope I γ (algebraMap A P) J hIJ)
variable (N : ℕ) (hN : Ideal.span {(p : E.D)} ^ N ≤ E.D.ideal)
variable (γhat : DividedPowers (RingHom.ker
  (AdicCompletion.toQuotient (Ideal.span {(p : E.D)}) E.D.ideal N hN)))
variable (hγhat : DividedPowers.IsDPMorphism E.D.dividedPowers γhat
  (algebraMap E.D (AdicCompletion (Ideal.span {(p : E.D)}) E.D)))
variable (e : ℕ)
variable (hstable : DividedPowers.IsSubDPIdeal E.D.dividedPowers
  (Ideal.span {(p : E.D)} ^ e ⊓ E.D.ideal))
variable (hstableHat : DividedPowers.IsSubDPIdeal
  (completionRing p A P I γ J hIJ E N hN γhat).dividedPowers
  (Ideal.span {(p : completionRing p A P I γ J hIJ E N hN γhat)} ^ e ⊓
    (completionRing p A P I γ J hIJ E N hN γhat).ideal))

#check (DividedPowers.PAdic.completionRing p A P I γ J hIJ E N hN γhat : DividedPowerRing)
#check (DividedPowers.PAdic.completionMap p A P I γ J hIJ E N hN γhat :
  E.D →+* completionRing p A P I γ J hIJ E N hN γhat)
#check (DividedPowers.PAdic.envelopeCompletionRing p A P I γ J hIJ E N hN γhat :
  DividedPowerRing)
#check (DividedPowers.PAdic.envelopeCompletionMap p A P I γ J hIJ E N hN γhat :
  E.D →+* envelopeCompletionRing p A P I γ J hIJ E N hN γhat)
#check (DividedPowers.PAdic.envelopeCompletionDividedPowers E N hN :
  DividedPowers (RingHom.ker
    (AdicCompletion.toQuotient (Ideal.span {(p : E.D)}) E.D.ideal N hN)))
#check (DividedPowers.PAdic.envelopeQuotient p A P I γ J hIJ E e hstable : DividedPowerRing)
#check (DividedPowers.PAdic.completionQuotient p A P I γ J hIJ E N hN γhat e hstableHat :
  DividedPowerRing)
#check (DividedPowers.PAdic.completionQuotientIsoEnvelopeQuotient p A P I γ J hIJ E N hN γhat
  hγhat e hstableHat hstable :
  completionQuotient p A P I γ J hIJ E N hN γhat e hstableHat ≅
    envelopeQuotient p A P I γ J hIJ E e hstable)

end DividedPowers.PAdic
