module

public import ReasLib.RingTheory.DividedPowers.Envelope.FiniteStage
public import ReasLib.RingTheory.DividedPowers.AdicCompletion
public import ReasLib.RingTheory.DividedPowers.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.Operations

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace DividedPowers.PAdic
variable (p : ℕ) [Fact (Nat.Prime p)]
variable (A P : Type u) [CommRing A] [CommRing P]
variable (I : Ideal A) (γ : DividedPowers I)
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable [Algebra A P]
variable (J : Ideal P) (hIJ : Ideal.map (algebraMap A P) I ≤ J)

/-- The divided-power ring on the principal-adic completion of an envelope. -/
def completionRing
    (E : DividedPowerEnvelope I γ (algebraMap A P) J hIJ)
    (N : ℕ) (hN : Ideal.span {(p : E.D)} ^ N ≤ E.D.ideal)
    (γhat : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : E.D)}) E.D.ideal N hN))) :
    DividedPowerRing :=
  DividedPowerRing.of (AdicCompletion (Ideal.span {(p : E.D)}) E.D)
    (RingHom.ker (AdicCompletion.toQuotient (Ideal.span {(p : E.D)}) E.D.ideal N hN)) γhat

/-- The canonical map from the envelope ring to its completed divided-power ring. -/
noncomputable def completionMap
    (E : DividedPowerEnvelope I γ (algebraMap A P) J hIJ)
    (N : ℕ) (hN : Ideal.span {(p : E.D)} ^ N ≤ E.D.ideal)
    (γhat : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : E.D)}) E.D.ideal N hN))) :
    E.D →+* completionRing p A P I γ J hIJ E N hN γhat :=
  algebraMap E.D (AdicCompletion (Ideal.span {(p : E.D)}) E.D)

/-- The completion map is the algebra map into the underlying adic completion. -/
theorem completionMap_spec
    (E : DividedPowerEnvelope I γ (algebraMap A P) J hIJ)
    (N : ℕ) (hN : Ideal.span {(p : E.D)} ^ N ≤ E.D.ideal)
    (γhat : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : E.D)}) E.D.ideal N hN))) :
    completionMap p A P I γ J hIJ E N hN γhat =
      algebraMap E.D (AdicCompletion (Ideal.span {(p : E.D)}) E.D) := sorry

/-- The distinguished ideal of `completionRing` is the kernel of its quotient map. -/
theorem completionRing_ideal
    (E : DividedPowerEnvelope I γ (algebraMap A P) J hIJ)
    (N : ℕ) (hN : Ideal.span {(p : E.D)} ^ N ≤ E.D.ideal)
    (γhat : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : E.D)}) E.D.ideal N hN))) :
    (completionRing p A P I γ J hIJ E N hN γhat).ideal =
      RingHom.ker (AdicCompletion.toQuotient
        (Ideal.span {(p : E.D)}) E.D.ideal N hN) := sorry

/-- The divided-power quotient of an envelope by the `e`th power of `(p)`. -/
def envelopeQuotient
    (E : DividedPowerEnvelope I γ (algebraMap A P) J hIJ)
    (e : ℕ)
    (hstable : DividedPowers.IsSubDPIdeal E.D.dividedPowers
      (Ideal.span {(p : E.D)} ^ e ⊓ E.D.ideal)) : DividedPowerRing :=
  DividedPowerRing.of (E.D ⧸ Ideal.span {(p : E.D)} ^ e)
    (Ideal.map (Ideal.Quotient.mk (Ideal.span {(p : E.D)} ^ e)) E.D.ideal)
    (DividedPowers.Quotient.dividedPowers E.D.dividedPowers hstable)

/-- The distinguished ideal of `envelopeQuotient` is the image of the envelope ideal. -/
theorem envelopeQuotient_ideal
    (E : DividedPowerEnvelope I γ (algebraMap A P) J hIJ)
    (e : ℕ)
    (hstable : DividedPowers.IsSubDPIdeal E.D.dividedPowers
      (Ideal.span {(p : E.D)} ^ e ⊓ E.D.ideal)) :
    (envelopeQuotient p A P I γ J hIJ E e hstable).ideal =
      Ideal.map (Ideal.Quotient.mk (Ideal.span {(p : E.D)} ^ e)) E.D.ideal := sorry

/-- The divided-power quotient of the completed envelope by the `e`th power of `(p)`. -/
def completionQuotient
    (E : DividedPowerEnvelope I γ (algebraMap A P) J hIJ)
    (N : ℕ) (hN : Ideal.span {(p : E.D)} ^ N ≤ E.D.ideal)
    (γhat : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : E.D)}) E.D.ideal N hN)))
    (e : ℕ)
    (hstableHat : DividedPowers.IsSubDPIdeal
      (completionRing p A P I γ J hIJ E N hN γhat).dividedPowers
      (Ideal.span {(p : completionRing p A P I γ J hIJ E N hN γhat)} ^ e ⊓
        (completionRing p A P I γ J hIJ E N hN γhat).ideal)) : DividedPowerRing :=
  DividedPowerRing.of
    (completionRing p A P I γ J hIJ E N hN γhat ⧸
      Ideal.span {(p : completionRing p A P I γ J hIJ E N hN γhat)} ^ e)
    ((completionRing p A P I γ J hIJ E N hN γhat).ideal.map
      (Ideal.Quotient.mk (Ideal.span
        {(p : completionRing p A P I γ J hIJ E N hN γhat)} ^ e)))
    (DividedPowers.Quotient.dividedPowers
      (completionRing p A P I γ J hIJ E N hN γhat).dividedPowers hstableHat)

/-- The distinguished ideal of `completionQuotient` is the induced completion ideal. -/
theorem completionQuotient_ideal
    (E : DividedPowerEnvelope I γ (algebraMap A P) J hIJ)
    (N : ℕ) (hN : Ideal.span {(p : E.D)} ^ N ≤ E.D.ideal)
    (γhat : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : E.D)}) E.D.ideal N hN)))
    (e : ℕ)
    (hstableHat : DividedPowers.IsSubDPIdeal
      (completionRing p A P I γ J hIJ E N hN γhat).dividedPowers
      (Ideal.span {(p : completionRing p A P I γ J hIJ E N hN γhat)} ^ e ⊓
        (completionRing p A P I γ J hIJ E N hN γhat).ideal)) :
    (completionQuotient p A P I γ J hIJ E N hN γhat e hstableHat).ideal =
      (completionRing p A P I γ J hIJ E N hN γhat).ideal.map
        (Ideal.Quotient.mk (Ideal.span
          {(p : completionRing p A P I γ J hIJ E N hN γhat)} ^ e)) := sorry

/-- Named application of the canonical completed envelope ring. -/
noncomputable abbrev envelopeCompletionRing
    (p : ℕ) [Fact (Nat.Prime p)]
    (A P : Type u) [CommRing A] [CommRing P]
    (I : Ideal A) (γ : DividedPowers I)
    [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
    [Algebra A P] (J : Ideal P)
    (hIJ : Ideal.map (algebraMap A P) I ≤ J)
    (E : DividedPowerEnvelope I γ (algebraMap A P) J hIJ)
    (N : ℕ) (hN : Ideal.span {(p : E.D)} ^ N ≤ E.D.ideal)
    (γhat : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : E.D)}) E.D.ideal N hN))) :
    DividedPowerRing :=
  completionRing p A P I γ J hIJ E N hN γhat
/-- The uniquely specified compatible divided powers on the principal-adic completion. -/
noncomputable def envelopeCompletionDividedPowers
    {p : ℕ} [Fact (Nat.Prime p)]
    {A P : Type u} [CommRing A] [CommRing P]
    {I : Ideal A} {γ : DividedPowers I}
    [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
    [Algebra A P] {J : Ideal P}
    {hIJ : Ideal.map (algebraMap A P) I ≤ J}
    (E : DividedPowerEnvelope I γ (algebraMap A P) J hIJ)
    (N : ℕ) (hN : Ideal.span {(p : E.D)} ^ N ≤ E.D.ideal) :
    DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : E.D)}) E.D.ideal N hN)) :=
  Classical.choose
    (ExistsUnique.exists
      (DividedPowers.existsUnique_principalCompletionExtension
        E.D.dividedPowers (p : E.D) N hN))

/-- The chosen extension is a divided-power morphism from the envelope. -/
theorem envelopeCompletionDividedPowers_isDPMorphism
    {p : ℕ} [Fact (Nat.Prime p)]
    {A P : Type u} [CommRing A] [CommRing P]
    {I : Ideal A} {γ : DividedPowers I}
    [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
    [Algebra A P] {J : Ideal P}
    {hIJ : Ideal.map (algebraMap A P) I ≤ J}
    (E : DividedPowerEnvelope I γ (algebraMap A P) J hIJ)
    (N : ℕ) (hN : Ideal.span {(p : E.D)} ^ N ≤ E.D.ideal) :
    DividedPowers.IsDPMorphism E.D.dividedPowers
      (envelopeCompletionDividedPowers E N hN)
      (algebraMap E.D (AdicCompletion (Ideal.span {(p : E.D)}) E.D)) := sorry

/-- Compatible divided powers on the envelope completion are unique. -/
theorem envelopeCompletionDividedPowers_unique
    {p : ℕ} [Fact (Nat.Prime p)]
    {A P : Type u} [CommRing A] [CommRing P]
    {I : Ideal A} {γ : DividedPowers I}
    [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
    [Algebra A P] {J : Ideal P}
    {hIJ : Ideal.map (algebraMap A P) I ≤ J}
    (E : DividedPowerEnvelope I γ (algebraMap A P) J hIJ)
    (N : ℕ) (hN : Ideal.span {(p : E.D)} ^ N ≤ E.D.ideal)
    (γhat : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : E.D)}) E.D.ideal N hN)))
    (hγhat : DividedPowers.IsDPMorphism E.D.dividedPowers γhat
      (algebraMap E.D (AdicCompletion (Ideal.span {(p : E.D)}) E.D))) :
    γhat = envelopeCompletionDividedPowers E N hN := sorry

/-- The completion map into `envelopeCompletionRing`. -/
noncomputable abbrev envelopeCompletionMap
    (p : ℕ) [Fact (Nat.Prime p)]
    (A P : Type u) [CommRing A] [CommRing P]
    (I : Ideal A) (γ : DividedPowers I)
    [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
    [Algebra A P] (J : Ideal P)
    (hIJ : Ideal.map (algebraMap A P) I ≤ J)
    (E : DividedPowerEnvelope I γ (algebraMap A P) J hIJ)
    (N : ℕ) (hN : Ideal.span {(p : E.D)} ^ N ≤ E.D.ideal)
    (γhat : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : E.D)}) E.D.ideal N hN))) :
    E.D →+* envelopeCompletionRing p A P I γ J hIJ E N hN γhat :=
  completionMap p A P I γ J hIJ E N hN γhat

/-- The quotient map from the completed envelope to the presented target. -/
noncomputable def envelopeCompletionToC
    (p : ℕ) [Fact (Nat.Prime p)]
    {A P C : Type u} [CommRing A] [CommRing P] [CommRing C]
    {I : Ideal A} {γ : DividedPowers I}
    [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
    [Algebra A P] (π : P →+* C) (hπ : Function.Surjective π)
    {J : Ideal P} (hJ : J = RingHom.ker π)
    {hIJ : Ideal.map (algebraMap A P) I ≤ J}
    (E : DividedPowerEnvelope I γ (algebraMap A P) J hIJ)
    (hE : DividedPowerEnvelope.IsUniversal γ (algebraMap A P) hIJ E)
    (N : ℕ) (hN : Ideal.span {(p : E.D)} ^ N ≤ E.D.ideal)
    (γhat : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : E.D)}) E.D.ideal N hN))) :
    envelopeCompletionRing p A P I γ J hIJ E N hN γhat →+* C :=
  (Ideal.Quotient.lift E.D.ideal (envelopeToC π hπ hJ E hE)
      (envelopeToC_ideal π hπ hJ E hE)).comp
    (AdicCompletion.toQuotient (Ideal.span {(p : E.D)}) E.D.ideal N hN)

/-- The divided-power base morphism into the completed envelope. -/
noncomputable def envelopeCompletionBase
    (p : ℕ) [Fact (Nat.Prime p)]
    {A P : Type u} [CommRing A] [CommRing P]
    {I : Ideal A} {γ : DividedPowers I}
    [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
    [Algebra A P] {J : Ideal P}
    {hIJ : Ideal.map (algebraMap A P) I ≤ J}
    (E : DividedPowerEnvelope I γ (algebraMap A P) J hIJ)
    (N : ℕ) (hN : Ideal.span {(p : E.D)} ^ N ≤ E.D.ideal)
    (γhat : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : E.D)}) E.D.ideal N hN)))
    (hγhat : DividedPowers.IsDPMorphism E.D.dividedPowers γhat
      (algebraMap E.D (AdicCompletion (Ideal.span {(p : E.D)}) E.D))) :
    DividedPowers.DPMorphism γ
      (envelopeCompletionRing p A P I γ J hIJ E N hN γhat).dividedPowers :=
  DividedPowers.DPMorphism.comp (DividedPowers.DPMorphism.mk' hγhat) E.base

/-- The induced completion quotient is surjective. -/
theorem envelopeCompletionToC_surjective
    (p : ℕ) [Fact (Nat.Prime p)]
    {A P C : Type u} [CommRing A] [CommRing P] [CommRing C]
    {I : Ideal A} {γ : DividedPowers I}
    [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
    [Algebra A P] (π : P →+* C) (hπ : Function.Surjective π)
    {J : Ideal P} (hJ : J = RingHom.ker π)
    {hIJ : Ideal.map (algebraMap A P) I ≤ J}
    (E : DividedPowerEnvelope I γ (algebraMap A P) J hIJ)
    (hE : DividedPowerEnvelope.IsUniversal γ (algebraMap A P) hIJ E)
    (N : ℕ) (hN : Ideal.span {(p : E.D)} ^ N ≤ E.D.ideal)
    (γhat : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : E.D)}) E.D.ideal N hN))) :
    Function.Surjective (envelopeCompletionToC p π hπ hJ E hE N hN γhat) := sorry

/-- The kernel of the induced completion quotient is the completed distinguished ideal. -/
theorem envelopeCompletionToC_ker
    (p : ℕ) [Fact (Nat.Prime p)]
    {A P C : Type u} [CommRing A] [CommRing P] [CommRing C]
    {I : Ideal A} {γ : DividedPowers I}
    [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
    [Algebra A P] (π : P →+* C) (hπ : Function.Surjective π)
    {J : Ideal P} (hJ : J = RingHom.ker π)
    {hIJ : Ideal.map (algebraMap A P) I ≤ J}
    (E : DividedPowerEnvelope I γ (algebraMap A P) J hIJ)
    (hE : DividedPowerEnvelope.IsUniversal γ (algebraMap A P) hIJ E)
    (N : ℕ) (hN : Ideal.span {(p : E.D)} ^ N ≤ E.D.ideal)
    (γhat : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : E.D)}) E.D.ideal N hN))) :
    RingHom.ker (envelopeCompletionToC p π hπ hJ E hE N hN γhat) =
      (envelopeCompletionRing p A P I γ J hIJ E N hN γhat).ideal := sorry

/-- The completed base and quotient maps make the base square commute. -/
theorem envelopeCompletionToC_comm
    (p : ℕ) [Fact (Nat.Prime p)]
    {A P C : Type u} [CommRing A] [CommRing P] [CommRing C]
    {I : Ideal A} {γ : DividedPowers I}
    [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
    [Algebra A P] (f : A →+* C) (π : P →+* C) (hπ : Function.Surjective π)
    (hπ_A : π.comp (algebraMap A P) = f)
    {J : Ideal P} (hJ : J = RingHom.ker π)
    {hIJ : Ideal.map (algebraMap A P) I ≤ J}
    (E : DividedPowerEnvelope I γ (algebraMap A P) J hIJ)
    (hE : DividedPowerEnvelope.IsUniversal γ (algebraMap A P) hIJ E)
    (N : ℕ) (hN : Ideal.span {(p : E.D)} ^ N ≤ E.D.ideal)
    (γhat : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : E.D)}) E.D.ideal N hN)))
    (hγhat : DividedPowers.IsDPMorphism E.D.dividedPowers γhat
      (algebraMap E.D (AdicCompletion (Ideal.span {(p : E.D)}) E.D))) :
    (envelopeCompletionToC p π hπ hJ E hE N hN γhat).comp
        (envelopeCompletionBase p E N hN γhat hγhat).toRingHom = f := sorry

/-- The envelope completion is p-adically complete. -/
theorem envelopeCompletion_isAdicComplete
    (p : ℕ) [Fact (Nat.Prime p)]
    {A P : Type u} [CommRing A] [CommRing P]
    {I : Ideal A} {γ : DividedPowers I}
    [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
    [Algebra A P] {J : Ideal P}
    {hIJ : Ideal.map (algebraMap A P) I ≤ J}
    (E : DividedPowerEnvelope I γ (algebraMap A P) J hIJ)
    (N : ℕ) (hN : Ideal.span {(p : E.D)} ^ N ≤ E.D.ideal)
    (γhat : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : E.D)}) E.D.ideal N hN))) :
    IsAdicComplete
      (Ideal.span
        ({(p : envelopeCompletionRing p A P I γ J hIJ E N hN γhat)} :
          Set (envelopeCompletionRing p A P I γ J hIJ E N hN γhat)))
      (envelopeCompletionRing p A P I γ J hIJ E N hN γhat) := sorry
variable (p : ℕ) [Fact (Nat.Prime p)]
variable (A P : Type u) [CommRing A] [CommRing P]
variable (I : Ideal A) (γ : DividedPowers I)
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable [Algebra A P]
variable (C : Type u) [CommRing C]
variable (f : A →+* C) (π : P →+* C)
variable (hπ_A : π.comp (algebraMap A P) = f)
variable (hIC : Ideal.map f I = (⊥ : Ideal C))
variable (J : Ideal P) (hJ : J = RingHom.ker π)
variable (hIJ : Ideal.map (algebraMap A P) I ≤ J)

/-- The principal powers of `p` in the envelope coincide with powers of the principal ideal. -/
theorem envelope_span_pow_eq (E : DividedPowerEnvelope I γ (algebraMap A P) J hIJ)
    (e : ℕ) :
    Ideal.span {(p : E.D)} ^ e = Ideal.span {((p : E.D) ^ e)} := sorry

/-- Evaluation from the completion through `p^e` annihilates the corresponding power of `p`. -/
theorem completionQuotient_toEnvelope_ker
    (E : DividedPowerEnvelope I γ (algebraMap A P) J hIJ)
    (N : ℕ) (hN : Ideal.span {(p : E.D)} ^ N ≤ E.D.ideal)
    (γhat : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : E.D)}) E.D.ideal N hN)))
    (e : ℕ) :
    Ideal.span {(p : completionRing p A P I γ J hIJ E N hN γhat)} ^ e ≤
      RingHom.ker
        (AdicCompletion.toQuotient (Ideal.span {(p : E.D)})
          (Ideal.span {(p : E.D)} ^ e) e le_rfl) := sorry

/-- The algebra map into the completion annihilates `p^e` after quotienting the completion. -/
theorem envelopeQuotient_toCompletion_ker
    (E : DividedPowerEnvelope I γ (algebraMap A P) J hIJ)
    (N : ℕ) (hN : Ideal.span {(p : E.D)} ^ N ≤ E.D.ideal)
    (γhat : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : E.D)}) E.D.ideal N hN)))
    (e : ℕ) :
    Ideal.span {(p : E.D)} ^ e ≤
      RingHom.ker
        ((Ideal.Quotient.mk
            (Ideal.span {(p : completionRing p A P I γ J hIJ E N hN γhat)} ^ e)).comp
          (completionMap p A P I γ J hIJ E N hN γhat)) := sorry

/-- The canonical ring map `D^∧ / p^e D^∧ → D / p^e D`. -/
noncomputable def completionQuotientToEnvelopeRingHom
    (E : DividedPowerEnvelope I γ (algebraMap A P) J hIJ)
    (N : ℕ) (hN : Ideal.span {(p : E.D)} ^ N ≤ E.D.ideal)
    (γhat : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : E.D)}) E.D.ideal N hN)))
    (e : ℕ)
    (hstableHat : DividedPowers.IsSubDPIdeal
      (completionRing p A P I γ J hIJ E N hN γhat).dividedPowers
      (Ideal.span {(p : completionRing p A P I γ J hIJ E N hN γhat)} ^ e ⊓
        (completionRing p A P I γ J hIJ E N hN γhat).ideal))
    (hstable : DividedPowers.IsSubDPIdeal E.D.dividedPowers
      (Ideal.span {(p : E.D)} ^ e ⊓ E.D.ideal)) :
    completionQuotient p A P I γ J hIJ E N hN γhat e hstableHat →+*
      envelopeQuotient p A P I γ J hIJ E e hstable :=
  Ideal.Quotient.lift _
    (AdicCompletion.toQuotient (Ideal.span {(p : E.D)})
      (Ideal.span {(p : E.D)} ^ e) e le_rfl)
    (completionQuotient_toEnvelope_ker p A P I γ J hIJ E N hN γhat e)

/-- The canonical ring map `D / p^e D → D^∧ / p^e D^∧`. -/
noncomputable def envelopeQuotientToCompletionRingHom
    (E : DividedPowerEnvelope I γ (algebraMap A P) J hIJ)
    (N : ℕ) (hN : Ideal.span {(p : E.D)} ^ N ≤ E.D.ideal)
    (γhat : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : E.D)}) E.D.ideal N hN)))
    (e : ℕ)
    (hstable : DividedPowers.IsSubDPIdeal E.D.dividedPowers
      (Ideal.span {(p : E.D)} ^ e ⊓ E.D.ideal))
    (hstableHat : DividedPowers.IsSubDPIdeal
      (completionRing p A P I γ J hIJ E N hN γhat).dividedPowers
      (Ideal.span {(p : completionRing p A P I γ J hIJ E N hN γhat)} ^ e ⊓
        (completionRing p A P I γ J hIJ E N hN γhat).ideal)) :
    envelopeQuotient p A P I γ J hIJ E e hstable →+*
      completionQuotient p A P I γ J hIJ E N hN γhat e hstableHat :=
  Ideal.Quotient.lift _
    ((Ideal.Quotient.mk
        (Ideal.span {(p : completionRing p A P I γ J hIJ E N hN γhat)} ^ e)).comp
      (completionMap p A P I γ J hIJ E N hN γhat))
    (envelopeQuotient_toCompletion_ker p A P I γ J hIJ E N hN γhat e)

/-- The ring map `D^∧ / p^e D^∧ → D / p^e D` preserves divided powers. -/
theorem completionQuotientToEnvelopeRingHom_isDPMorphism
    (E : DividedPowerEnvelope I γ (algebraMap A P) J hIJ)
    (N : ℕ) (hN : Ideal.span {(p : E.D)} ^ N ≤ E.D.ideal)
    (γhat : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : E.D)}) E.D.ideal N hN)))
    (hγhat : DividedPowers.IsDPMorphism E.D.dividedPowers γhat
      (algebraMap E.D (AdicCompletion (Ideal.span {(p : E.D)}) E.D)))
    (e : ℕ)
    (hstableHat : DividedPowers.IsSubDPIdeal
      (completionRing p A P I γ J hIJ E N hN γhat).dividedPowers
      (Ideal.span {(p : completionRing p A P I γ J hIJ E N hN γhat)} ^ e ⊓
        (completionRing p A P I γ J hIJ E N hN γhat).ideal))
    (hstable : DividedPowers.IsSubDPIdeal E.D.dividedPowers
      (Ideal.span {(p : E.D)} ^ e ⊓ E.D.ideal)) :
    DividedPowers.IsDPMorphism
      (completionQuotient p A P I γ J hIJ E N hN γhat e hstableHat).dividedPowers
      (envelopeQuotient p A P I γ J hIJ E e hstable).dividedPowers
      (completionQuotientToEnvelopeRingHom p A P I γ J hIJ E N hN γhat e
        hstableHat hstable) := sorry

/-- The ring map `D / p^e D → D^∧ / p^e D^∧` preserves divided powers. -/
theorem envelopeQuotientToCompletionRingHom_isDPMorphism
    (E : DividedPowerEnvelope I γ (algebraMap A P) J hIJ)
    (N : ℕ) (hN : Ideal.span {(p : E.D)} ^ N ≤ E.D.ideal)
    (γhat : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : E.D)}) E.D.ideal N hN)))
    (hγhat : DividedPowers.IsDPMorphism E.D.dividedPowers γhat
      (algebraMap E.D (AdicCompletion (Ideal.span {(p : E.D)}) E.D)))
    (e : ℕ)
    (hstable : DividedPowers.IsSubDPIdeal E.D.dividedPowers
      (Ideal.span {(p : E.D)} ^ e ⊓ E.D.ideal))
    (hstableHat : DividedPowers.IsSubDPIdeal
      (completionRing p A P I γ J hIJ E N hN γhat).dividedPowers
      (Ideal.span {(p : completionRing p A P I γ J hIJ E N hN γhat)} ^ e ⊓
        (completionRing p A P I γ J hIJ E N hN γhat).ideal)) :
    DividedPowers.IsDPMorphism
      (envelopeQuotient p A P I γ J hIJ E e hstable).dividedPowers
      (completionQuotient p A P I γ J hIJ E N hN γhat e hstableHat).dividedPowers
      (envelopeQuotientToCompletionRingHom p A P I γ J hIJ E N hN γhat e
        hstable hstableHat) := sorry

/-- The named divided-power morphism `D^∧ / p^e D^∧ ⟶ D / p^e D`. -/
noncomputable def completionQuotientToEnvelopeQuotient
    (E : DividedPowerEnvelope I γ (algebraMap A P) J hIJ)
    (N : ℕ) (hN : Ideal.span {(p : E.D)} ^ N ≤ E.D.ideal)
    (γhat : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : E.D)}) E.D.ideal N hN)))
    (hγhat : DividedPowers.IsDPMorphism E.D.dividedPowers γhat
      (algebraMap E.D (AdicCompletion (Ideal.span {(p : E.D)}) E.D)))
    (e : ℕ)
    (hstableHat : DividedPowers.IsSubDPIdeal
      (completionRing p A P I γ J hIJ E N hN γhat).dividedPowers
      (Ideal.span {(p : completionRing p A P I γ J hIJ E N hN γhat)} ^ e ⊓
        (completionRing p A P I γ J hIJ E N hN γhat).ideal))
    (hstable : DividedPowers.IsSubDPIdeal E.D.dividedPowers
      (Ideal.span {(p : E.D)} ^ e ⊓ E.D.ideal)) :
    completionQuotient p A P I γ J hIJ E N hN γhat e hstableHat ⟶
      envelopeQuotient p A P I γ J hIJ E e hstable :=
  DividedPowers.DPMorphism.mk'
    (completionQuotientToEnvelopeRingHom_isDPMorphism p A P I γ J hIJ E N hN γhat hγhat e
      hstableHat hstable)

/-- The named divided-power morphism `D / p^e D ⟶ D^∧ / p^e D^∧`. -/
noncomputable def envelopeQuotientToCompletionQuotient
    (E : DividedPowerEnvelope I γ (algebraMap A P) J hIJ)
    (N : ℕ) (hN : Ideal.span {(p : E.D)} ^ N ≤ E.D.ideal)
    (γhat : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : E.D)}) E.D.ideal N hN)))
    (hγhat : DividedPowers.IsDPMorphism E.D.dividedPowers γhat
      (algebraMap E.D (AdicCompletion (Ideal.span {(p : E.D)}) E.D)))
    (e : ℕ)
    (hstable : DividedPowers.IsSubDPIdeal E.D.dividedPowers
      (Ideal.span {(p : E.D)} ^ e ⊓ E.D.ideal))
    (hstableHat : DividedPowers.IsSubDPIdeal
      (completionRing p A P I γ J hIJ E N hN γhat).dividedPowers
      (Ideal.span {(p : completionRing p A P I γ J hIJ E N hN γhat)} ^ e ⊓
        (completionRing p A P I γ J hIJ E N hN γhat).ideal)) :
    envelopeQuotient p A P I γ J hIJ E e hstable ⟶
      completionQuotient p A P I γ J hIJ E N hN γhat e hstableHat :=
  DividedPowers.DPMorphism.mk'
    (envelopeQuotientToCompletionRingHom_isDPMorphism p A P I γ J hIJ E N hN γhat hγhat e
      hstable hstableHat)

/-- The comparison to the ordinary quotient followed by the reverse comparison is the identity on the completed quotient. -/
theorem completionQuotient_hom_inv_id
    (E : DividedPowerEnvelope I γ (algebraMap A P) J hIJ)
    (N : ℕ) (hN : Ideal.span {(p : E.D)} ^ N ≤ E.D.ideal)
    (γhat : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : E.D)}) E.D.ideal N hN)))
    (hγhat : DividedPowers.IsDPMorphism E.D.dividedPowers γhat
      (algebraMap E.D (AdicCompletion (Ideal.span {(p : E.D)}) E.D)))
    (e : ℕ)
    (hstableHat : DividedPowers.IsSubDPIdeal
      (completionRing p A P I γ J hIJ E N hN γhat).dividedPowers
      (Ideal.span {(p : completionRing p A P I γ J hIJ E N hN γhat)} ^ e ⊓
        (completionRing p A P I γ J hIJ E N hN γhat).ideal))
    (hstable : DividedPowers.IsSubDPIdeal E.D.dividedPowers
      (Ideal.span {(p : E.D)} ^ e ⊓ E.D.ideal)) :
    completionQuotientToEnvelopeQuotient p A P I γ J hIJ E N hN γhat hγhat e
        hstableHat hstable ≫
      envelopeQuotientToCompletionQuotient p A P I γ J hIJ E N hN γhat hγhat e
        hstable hstableHat = 𝟙 _ := sorry

/-- The reverse comparison followed by the comparison to the ordinary quotient is the identity on the ordinary quotient. -/
theorem completionQuotient_inv_hom_id
    (E : DividedPowerEnvelope I γ (algebraMap A P) J hIJ)
    (N : ℕ) (hN : Ideal.span {(p : E.D)} ^ N ≤ E.D.ideal)
    (γhat : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : E.D)}) E.D.ideal N hN)))
    (hγhat : DividedPowers.IsDPMorphism E.D.dividedPowers γhat
      (algebraMap E.D (AdicCompletion (Ideal.span {(p : E.D)}) E.D)))
    (e : ℕ)
    (hstableHat : DividedPowers.IsSubDPIdeal
      (completionRing p A P I γ J hIJ E N hN γhat).dividedPowers
      (Ideal.span {(p : completionRing p A P I γ J hIJ E N hN γhat)} ^ e ⊓
        (completionRing p A P I γ J hIJ E N hN γhat).ideal))
    (hstable : DividedPowers.IsSubDPIdeal E.D.dividedPowers
      (Ideal.span {(p : E.D)} ^ e ⊓ E.D.ideal)) :
    envelopeQuotientToCompletionQuotient p A P I γ J hIJ E N hN γhat hγhat e
        hstable hstableHat ≫
      completionQuotientToEnvelopeQuotient p A P I γ J hIJ E N hN γhat hγhat e
        hstableHat hstable = 𝟙 _ := sorry

/-- The canonical divided-power isomorphism between the completed and ordinary quotients. -/
noncomputable def completionQuotientIsoEnvelopeQuotient
    (E : DividedPowerEnvelope I γ (algebraMap A P) J hIJ)
    (N : ℕ) (hN : Ideal.span {(p : E.D)} ^ N ≤ E.D.ideal)
    (γhat : DividedPowers (RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : E.D)}) E.D.ideal N hN)))
    (hγhat : DividedPowers.IsDPMorphism E.D.dividedPowers γhat
      (algebraMap E.D (AdicCompletion (Ideal.span {(p : E.D)}) E.D)))
    (e : ℕ)
    (hstableHat : DividedPowers.IsSubDPIdeal
      (completionRing p A P I γ J hIJ E N hN γhat).dividedPowers
      (Ideal.span {(p : completionRing p A P I γ J hIJ E N hN γhat)} ^ e ⊓
        (completionRing p A P I γ J hIJ E N hN γhat).ideal))
    (hstable : DividedPowers.IsSubDPIdeal E.D.dividedPowers
      (Ideal.span {(p : E.D)} ^ e ⊓ E.D.ideal)) :
    completionQuotient p A P I γ J hIJ E N hN γhat e hstableHat ≅
      envelopeQuotient p A P I γ J hIJ E e hstable where
  hom := completionQuotientToEnvelopeQuotient p A P I γ J hIJ E N hN γhat hγhat e
    hstableHat hstable
  inv := envelopeQuotientToCompletionQuotient p A P I γ J hIJ E N hN γhat hγhat e
    hstable hstableHat
  hom_inv_id := completionQuotient_hom_inv_id p A P I γ J hIJ E N hN γhat hγhat e
    hstableHat hstable
  inv_hom_id := completionQuotient_inv_hom_id p A P I γ J hIJ E N hN γhat hγhat e
    hstableHat hstable

end DividedPowers.PAdic
