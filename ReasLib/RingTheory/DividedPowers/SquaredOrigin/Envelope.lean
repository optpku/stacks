/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DividedPowers.SquaredOrigin.Algebra
public import ReasLib.RingTheory.DividedPowers.Envelope.Crystalline
public import ReasLib.RingTheory.DividedPowers.DeRham.CrystallineOmega
public import Mathlib.RingTheory.AdicCompletion.Algebra

@[expose] public section

noncomputable section

open CategoryTheory DividedPowers

namespace Crystalline.SquaredOrigin

/-- The principal-adic completion of a divided-power envelope of the squared origin. -/
abbrev envelopeD (p : ℕ) [Fact p.Prime]
    (E : DividedPowerEnvelope (padicIdeal p) (PadicInt.dividedPowers p)
      (algebraMap ℤ_[p] (polynomialRing p)) (presentationIdeal p) (primeMap_le p))
    (hE : DividedPowerEnvelope.IsUniversal (PadicInt.dividedPowers p)
      (algebraMap ℤ_[p] (polynomialRing p)) (primeMap_le p) E) : Type :=
  AdicCompletion (Ideal.span {(p : E.D)}) E.D

/-- The prime ideal of an envelope lies in its distinguished divided-power ideal. -/
theorem envelope_prime_le {p : ℕ} [Fact p.Prime]
    (E : DividedPowerEnvelope (padicIdeal p) (PadicInt.dividedPowers p)
      (algebraMap ℤ_[p] (polynomialRing p)) (presentationIdeal p) (primeMap_le p)) :
    Ideal.span {(p : E.D)} ^ 1 ≤ E.D.ideal := sorry

/-- The image of the envelope ideal in its principal-adic completion. -/
def completedIdeal (p : ℕ) [Fact p.Prime]
    (E : DividedPowerEnvelope (padicIdeal p) (PadicInt.dividedPowers p)
      (algebraMap ℤ_[p] (polynomialRing p)) (presentationIdeal p) (primeMap_le p))
    (hE : DividedPowerEnvelope.IsUniversal (PadicInt.dividedPowers p)
      (algebraMap ℤ_[p] (polynomialRing p)) (primeMap_le p) E) : Ideal (envelopeD p E hE) :=
  Ideal.map (algebraMap E.D (envelopeD p E hE)) E.D.ideal

/-- The completed image ideal is the kernel of the completed quotient map. -/
theorem completedIdeal_eq_kernel {p : ℕ} [Fact p.Prime]
    (E : DividedPowerEnvelope (padicIdeal p) (PadicInt.dividedPowers p)
      (algebraMap ℤ_[p] (polynomialRing p)) (presentationIdeal p) (primeMap_le p))
    (hE : DividedPowerEnvelope.IsUniversal (PadicInt.dividedPowers p)
      (algebraMap ℤ_[p] (polynomialRing p)) (primeMap_le p) E) :
    completedIdeal p E hE = RingHom.ker
      (AdicCompletion.toQuotient (Ideal.span {(p : E.D)}) E.D.ideal 1
        (envelope_prime_le E)) := sorry

/-- An explicit universal envelope model with divided powers extending to its completion. -/
structure EnvelopeData (p : ℕ) [Fact p.Prime] where
  /-- The uncompleted envelope diagram. -/
  E : DividedPowerEnvelope (padicIdeal p) (PadicInt.dividedPowers p)
    (algebraMap ℤ_[p] (polynomialRing p)) (presentationIdeal p) (primeMap_le p)
  /-- Every compatible divided-power map has a unique lift. -/
  hE : DividedPowerEnvelope.IsUniversal (PadicInt.dividedPowers p)
    (algebraMap ℤ_[p] (polynomialRing p)) (primeMap_le p) E
  /-- Divided powers on the completed image ideal. -/
  γbar : DividedPowers (completedIdeal p E hE)
  /-- Completion preserves the envelope divided powers. -/
  hγbar : IsDPMorphism E.D.dividedPowers γbar (algebraMap E.D (envelopeD p E hE))

/-- Construct an explicit universal envelope model with completed divided powers. -/
def EnvelopeData.of (p : ℕ) [Fact p.Prime]
    (E : DividedPowerEnvelope (padicIdeal p) (PadicInt.dividedPowers p)
      (algebraMap ℤ_[p] (polynomialRing p)) (presentationIdeal p) (primeMap_le p))
    (hE : DividedPowerEnvelope.IsUniversal (PadicInt.dividedPowers p)
      (algebraMap ℤ_[p] (polynomialRing p)) (primeMap_le p) E)
    (γbar : DividedPowers (completedIdeal p E hE))
    (hγbar : IsDPMorphism E.D.dividedPowers γbar (algebraMap E.D (envelopeD p E hE))) :
    EnvelopeData p :=
  ⟨E, hE, γbar, hγbar⟩

/-- Universality and preservation of divided powers under completion hold together. -/
theorem EnvelopeData.spec {p : ℕ} [Fact p.Prime] (data : EnvelopeData p) :
    DividedPowerEnvelope.IsUniversal (PadicInt.dividedPowers p)
        (algebraMap ℤ_[p] (polynomialRing p)) (primeMap_le p) data.E ∧
      IsDPMorphism data.E.D.dividedPowers data.γbar
        (algebraMap data.E.D (envelopeD p data.E data.hE)) := sorry

/-- The completed ring of an explicit envelope model. -/
abbrev EnvelopeData.D {p : ℕ} [Fact p.Prime] (data : EnvelopeData p) : Type :=
  envelopeD p data.E data.hE

/-- The canonical polynomial map into the completed envelope. -/
def polynomialToCompleted {p : ℕ} [Fact p.Prime] (data : EnvelopeData p) :
    polynomialRing p →+* data.D :=
  (algebraMap data.E.D data.D).comp data.E.toD

/-- The completed image of the first polynomial coordinate. -/
def EnvelopeData.x {p : ℕ} [Fact p.Prime] (data : EnvelopeData p) : data.D :=
  polynomialToCompleted data (MvPolynomial.X Coord.x)

/-- The completed image of the second polynomial coordinate. -/
def EnvelopeData.y {p : ℕ} [Fact p.Prime] (data : EnvelopeData p) : data.D :=
  polynomialToCompleted data (MvPolynomial.X Coord.y)

/-- The coefficient map into the completed envelope. -/
def envelopeBaseMap {p : ℕ} [Fact p.Prime] (data : EnvelopeData p) : ℤ_[p] →+* data.D :=
  (polynomialToCompleted data).comp (algebraMap ℤ_[p] (polynomialRing p))

/-- The completed crystalline object obtained from the universal envelope model. -/
def EnvelopeData.completedObject {p : ℕ} [Fact p.Prime] (data : EnvelopeData p) :=
  DividedPowers.PAdic.envelopeCompletedCrisObject p (PadicInt.dividedPowers p)
    (algebraMap ℤ_[p] (coordinateRing p)) (presentation p).toRingHom
    (presentation_surjective p) (presentation p).comp_algebraMap
    (coordinate_prime_bot p) (coordinate_p_nilpotent p) (ker_presentation p).symm
    data.E data.hE 1 (envelope_prime_le data.E)
    ((completedIdeal_eq_kernel data.E data.hE) ▸ data.γbar)
    (Eq.rec (motive := fun J h ↦ IsDPMorphism data.E.D.dividedPowers
      (h ▸ data.γbar) (algebraMap data.E.D data.D)) data.hγbar
      (completedIdeal_eq_kernel data.E data.hE))

/-- The difference of the two degree-`p` divided-power products at the squared origin. -/
def tau {p : ℕ} [Fact p.Prime] (data : EnvelopeData p) : data.D :=
  data.γbar.dpow p (data.x ^ 2) * data.γbar.dpow p (data.y ^ 2) -
    data.γbar.dpow p (data.x * data.y) ^ 2

/-- Polynomial Frobenius is compatible with the base divided powers in the envelope. -/
theorem envelopeFrobenius_baseCompatible {p : ℕ} [Fact p.Prime] (data : EnvelopeData p) :
    IsDPMorphism (PadicInt.dividedPowers p) data.E.D.dividedPowers
      ((data.E.toD.comp (polynomialFrobenius p).toRingHom).comp
        (algebraMap ℤ_[p] (polynomialRing p))) := sorry

/-- Polynomial Frobenius sends the presentation ideal into the envelope ideal. -/
theorem envelopeFrobenius_idealMap {p : ℕ} [Fact p.Prime] (data : EnvelopeData p) :
    Ideal.map (data.E.toD.comp (polynomialFrobenius p).toRingHom) (presentationIdeal p) ≤
      data.E.D.ideal := sorry

/-- The uniquely specified divided-power lift of polynomial Frobenius to the envelope. -/
def envelopeFrobenius {p : ℕ} [Fact p.Prime] (data : EnvelopeData p) : data.E.D ⟶ data.E.D :=
  Classical.choose (data.hE (data.E.toD.comp (polynomialFrobenius p).toRingHom)
    (envelopeFrobenius_baseCompatible data) (envelopeFrobenius_idealMap data)).exists

/-- The envelope Frobenius restricts to polynomial Frobenius and is the unique such lift. -/
theorem envelopeFrobenius_spec {p : ℕ} [Fact p.Prime] (data : EnvelopeData p) :
    (envelopeFrobenius data).toRingHom.comp data.E.toD =
        data.E.toD.comp (polynomialFrobenius p).toRingHom ∧
      ∀ ψ : data.E.D ⟶ data.E.D,
        ψ.toRingHom.comp data.E.toD = data.E.toD.comp (polynomialFrobenius p).toRingHom →
          ψ = envelopeFrobenius data := sorry

/-- Envelope Frobenius descends to every principal-adic quotient. -/
theorem envelopeFrobenius_adic {p : ℕ} [Fact p.Prime] (data : EnvelopeData p) :
    ∀ n, Ideal.span {(p : data.E.D)} ^ n ≤ RingHom.ker
      ((Ideal.Quotient.mk (Ideal.span {(p : data.E.D)} ^ n)).comp
        (envelopeFrobenius data).toRingHom) := sorry

/-- Frobenius on each principal-adic quotient of the envelope. -/
def envelopeFrobeniusQuotient {p : ℕ} [Fact p.Prime] (data : EnvelopeData p) (n : ℕ) :
    (data.E.D ⧸ Ideal.span {(p : data.E.D)} ^ n) →+*
      data.E.D ⧸ Ideal.span {(p : data.E.D)} ^ n :=
  Ideal.Quotient.lift _
    ((Ideal.Quotient.mk _).comp (envelopeFrobenius data).toRingHom)
    (fun a ha ↦ envelopeFrobenius_adic data n ha)

/-- Quotient Frobenius maps form a compatible family on the completion. -/
theorem envelopeFrobeniusQuotient_compatible {p : ℕ} [Fact p.Prime]
    (data : EnvelopeData p) {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (Ideal.span {(p : data.E.D)}) hle).comp
        ((envelopeFrobeniusQuotient data n).comp
          (AdicCompletion.evalₐ (Ideal.span {(p : data.E.D)}) n).toRingHom) =
      (envelopeFrobeniusQuotient data m).comp
        (AdicCompletion.evalₐ (Ideal.span {(p : data.E.D)}) m).toRingHom := sorry

/-- The endomorphism of the completion induced by compatible quotient Frobenius maps. -/
def completedFrobenius {p : ℕ} [Fact p.Prime] (data : EnvelopeData p) : data.D →+* data.D :=
  AdicCompletion.liftRingHom (Ideal.span {(p : data.E.D)})
    (fun n ↦ (envelopeFrobeniusQuotient data n).comp
      (AdicCompletion.evalₐ (Ideal.span {(p : data.E.D)}) n).toRingHom)
    (envelopeFrobeniusQuotient_compatible data)

/-- Completed Frobenius extends polynomial Frobenius and preserves divided powers. -/
theorem completedFrobenius_spec {p : ℕ} [Fact p.Prime] (data : EnvelopeData p) :
    (completedFrobenius data).comp (polynomialToCompleted data) =
        (polynomialToCompleted data).comp (polynomialFrobenius p).toRingHom ∧
      IsDPMorphism data.γbar data.γbar (completedFrobenius data) := sorry

/-- The polynomial witness map is compatible with the base divided powers. -/
theorem envelopeToWitness_baseCompatible {p : ℕ} [Fact p.Prime] (data : EnvelopeData p)
    (δ : DividedPowers (RingHom.ker (witnessToCoordinate p)))
    (hδ : δ.dpowPrime p = witnessDpowPrime p) :
    IsDPMorphism (PadicInt.dividedPowers p) δ
      ((polynomialToWitness p).comp (algebraMap ℤ_[p] (polynomialRing p))) := sorry

/-- The polynomial witness map sends the presentation ideal to the witness kernel. -/
theorem envelopeToWitness_idealMap {p : ℕ} [Fact p.Prime] (data : EnvelopeData p) :
    Ideal.map (polynomialToWitness p) (presentationIdeal p) ≤
      RingHom.ker (witnessToCoordinate p) := sorry

/-- The uniquely specified divided-power map from the envelope to the witness ring. -/
def envelopeToWitness {p : ℕ} [Fact p.Prime] (data : EnvelopeData p)
    (δ : DividedPowers (RingHom.ker (witnessToCoordinate p)))
    (hδ : δ.dpowPrime p = witnessDpowPrime p) : data.E.D ⟶ witnessDPRing p δ :=
  Classical.choose (data.hE (T := witnessDPRing p δ) (polynomialToWitness p)
    (envelopeToWitness_baseCompatible data δ hδ) (envelopeToWitness_idealMap data)).exists

/-- The witness map restricts to the specified polynomial map and is its unique lift. -/
theorem envelopeToWitness_spec {p : ℕ} [Fact p.Prime] (data : EnvelopeData p)
    (δ : DividedPowers (RingHom.ker (witnessToCoordinate p)))
    (hδ : δ.dpowPrime p = witnessDpowPrime p) :
    (envelopeToWitness data δ hδ).toRingHom.comp data.E.toD = polynomialToWitness p ∧
      ∀ ψ : data.E.D ⟶ witnessDPRing p δ,
        ψ.toRingHom.comp data.E.toD = polynomialToWitness p →
          ψ = envelopeToWitness data δ hδ := sorry

/-- The envelope map to the characteristic-`p` witness annihilates the prime ideal. -/
theorem envelopeToWitness_adicKernel {p : ℕ} [Fact p.Prime] (data : EnvelopeData p)
    (δ : DividedPowers (RingHom.ker (witnessToCoordinate p)))
    (hδ : δ.dpowPrime p = witnessDpowPrime p) :
    Ideal.span {(p : data.E.D)} ≤ RingHom.ker (envelopeToWitness data δ hδ).toRingHom := sorry

/-- The witness map descended through the quotient of the envelope by the prime ideal. -/
def envelopeWitnessQuotient {p : ℕ} [Fact p.Prime] (data : EnvelopeData p)
    (δ : DividedPowers (RingHom.ker (witnessToCoordinate p)))
    (hδ : δ.dpowPrime p = witnessDpowPrime p) :
    (data.E.D ⧸ Ideal.span {(p : data.E.D)}) →+* witnessRing p :=
  Ideal.Quotient.lift _ (envelopeToWitness data δ hδ).toRingHom
    (fun a ha ↦ envelopeToWitness_adicKernel data δ hδ ha)

/-- The comparison from the completed envelope to the witness via its first quotient. -/
def completedToWitness {p : ℕ} [Fact p.Prime] (data : EnvelopeData p)
    (δ : DividedPowers (RingHom.ker (witnessToCoordinate p)))
    (hδ : δ.dpowPrime p = witnessDpowPrime p) : data.D →+* witnessRing p :=
  (envelopeWitnessQuotient data δ hδ).comp
    (AdicCompletion.evalOneₐ (Ideal.span {(p : data.E.D)})).toRingHom

/-- The completed witness comparison extends the polynomial map and preserves divided powers. -/
theorem completedToWitness_spec {p : ℕ} [Fact p.Prime] (data : EnvelopeData p)
    (δ : DividedPowers (RingHom.ker (witnessToCoordinate p)))
    (hδ : δ.dpowPrime p = witnessDpowPrime p) :
    (completedToWitness data δ hδ).comp (polynomialToCompleted data) = polynomialToWitness p ∧
      IsDPMorphism data.γbar δ (completedToWitness data δ hδ) := sorry

/-- A compatible divided-power witness map sends the distinguished element to `uv`. -/
theorem tau_maps_to_uv {p : ℕ} [Fact p.Prime] (data : EnvelopeData p)
    (δ : DividedPowers (RingHom.ker (witnessToCoordinate p)))
    (hδ : δ.dpowPrime p = witnessDpowPrime p)
    (ψ : data.D →+* witnessRing p)
    (hext : ψ.comp (polynomialToCompleted data) = polynomialToWitness p)
    (hdp : IsDPMorphism data.γbar δ ψ) : ψ (tau data) = witnessUv p := sorry

/-- The distinguished completed-envelope element is killed by the prime. -/
theorem tau_p_mul {p : ℕ} [Fact p.Prime] (data : EnvelopeData p) :
    (p : data.D) * tau data = 0 := sorry

/-- The distinguished completed-envelope element has zero completed relative differential. -/
theorem tau_differential {p : ℕ} [Fact p.Prime] (data : EnvelopeData p) :
    crystallineOmegaD_derivation (envelopeBaseMap data) data.γbar p (tau data) = 0 := sorry

/-- The distinguished completed-envelope element is nonzero. -/
theorem tau_ne_zero {p : ℕ} [Fact p.Prime] (data : EnvelopeData p) : tau data ≠ 0 := sorry

/-- Completed polynomial Frobenius kills the distinguished element. -/
theorem sigma_tau {p : ℕ} [Fact p.Prime] (data : EnvelopeData p) :
    completedFrobenius data (tau data) = 0 := sorry

/-- The additive subgroup of elements with zero completed relative differential. -/
def closedForms {p : ℕ} [Fact p.Prime] (data : EnvelopeData p) : AddSubgroup data.D :=
  (crystallineOmegaD_derivation (envelopeBaseMap data) data.γbar p).toAddMonoidHom.ker

/-- The abelian group of closed elements of the completed envelope. -/
def deRhamH0 {p : ℕ} [Fact p.Prime] (data : EnvelopeData p) : AddCommGrpCat.{0} :=
  .of (closedForms data)

/-- Completed Frobenius preserves the kernel of the completed derivation. -/
theorem completedFrobenius_preserves_closedForms {p : ℕ} [Fact p.Prime]
    (data : EnvelopeData p) (z : data.D) (hz : z ∈ closedForms data) :
    completedFrobenius data z ∈ closedForms data := sorry

/-- The restriction of completed Frobenius to closed elements. -/
def frobeniusOnClosedForms {p : ℕ} [Fact p.Prime] (data : EnvelopeData p) :
    closedForms data →+ closedForms data :=
  ((completedFrobenius data).toAddMonoidHom.restrict (closedForms data)).codRestrict
    (closedForms data) (fun z ↦ completedFrobenius_preserves_closedForms data z z.property)

end Crystalline.SquaredOrigin
