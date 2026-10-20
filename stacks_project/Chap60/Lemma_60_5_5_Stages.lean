module

public import ReasLib.RingTheory.DividedPowers.Envelope.FiniteStage

open DividedPowers

@[expose] public section

universe u

namespace DividedPowers.PAdic

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (A P : Type u) [CommRing A] [CommRing P]
variable (I : Ideal A) (γ : DividedPowers I)
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable [Algebra A P]
variable (J : Ideal P)
variable (hIJ : Ideal.map (algebraMap A P) I ≤ J)
variable (C : Type u) [CommRing C]
variable (π : P →+* C) (hπ : Function.Surjective π)
variable (hJ : J = RingHom.ker π)

#check (DividedPowers.PAdic.quotient p P : ℕ → Type u)
#check (DividedPowers.PAdic.stageIdeal p P J : ∀ e : ℕ, Ideal (quotient p P e))
#check (DividedPowers.PAdic.stageMap p A P : ∀ e : ℕ, A →+* quotient p P e)
#check (DividedPowers.PAdic.envelopeStage p A P I γ J :
  (hIJ : Ideal.map (algebraMap A P) I ≤ J) →
    ∀ e : ℕ, Type (u + 1))
#check (DividedPowers.PAdic.envelopeStageFromP p :
  ∀ {hIJ : Ideal.map (algebraMap A P) I ≤ J} (e : ℕ)
    (EStage : envelopeStage p A P I γ J hIJ e), P →+* EStage.D)
#check (DividedPowers.PAdic.envelopeStageQuotientMap p :
  ∀ {A P C : Type u} [CommRing A] [CommRing P] [CommRing C]
    {I : Ideal A} {γ : DividedPowers I}
    [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
    [Algebra A P] (π : P →+* C) (hπ : Function.Surjective π)
    {J : Ideal P} (hJ : J = RingHom.ker π)
    {hIJ : Ideal.map (algebraMap A P) I ≤ J} (e : ℕ)
    (EStage : envelopeStage p A P I γ J hIJ e),
    C →+* (EStage.D ⧸ EStage.D.ideal))

end DividedPowers.PAdic
