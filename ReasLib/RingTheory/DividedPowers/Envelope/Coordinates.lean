/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DividedPowers.Envelope.Differential
public import ReasLib.RingTheory.DividedPowers.Envelope.Completion
public import ReasLib.RingTheory.AdicCompletion.PrincipalMaps
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

@[expose] public section

set_option backward.privateInPublic true

noncomputable section

open scoped TensorProduct
open KaehlerDifferential.DeRham

universe u

namespace DividedPowerEnvelope.Coordinates

variable {A ι : Type u} [CommRing A] {I : Ideal A} {γ : DividedPowers I}
variable {J : Ideal (MvPolynomial ι A)}
variable {hIJ : Ideal.map (algebraMap A (MvPolynomial ι A)) I ≤ J}
variable (E : DividedPowerEnvelope I γ (algebraMap A (MvPolynomial ι A)) J hIJ)
variable (hE : IsUniversal γ (algebraMap A (MvPolynomial ι A)) hIJ E)

/-- The polynomial algebra action selected by an explicit envelope. -/
@[implicit_reducible] def polynomialAlgebra : Algebra (MvPolynomial ι A) E.D := E.toD.toAlgebra

/-- The coefficient algebra action on an explicit polynomial envelope. -/
@[implicit_reducible] def baseAlgebra : Algebra A E.D :=
  (E.toD.comp (algebraMap A (MvPolynomial ι A))).toAlgebra

/-- The coefficient action factors through the polynomial algebra. -/
@[implicit_reducible] def baseTower :
    -- Local instance justification (noncanonical choice): E.toD selects the polynomial action in this tower.
    letI := polynomialAlgebra E
    -- Local instance justification (noncanonical choice): the composite E.toD selects the coefficient action in this tower.
    letI := baseAlgebra E
    IsScalarTower A (MvPolynomial ι A) E.D :=
  -- Local instance justification (noncanonical choice): E.toD selects the polynomial action in this tower.
  letI := polynomialAlgebra E
  -- Local instance justification (noncanonical choice): the composite E.toD selects the coefficient action in this tower.
  letI := baseAlgebra E
  IsScalarTower.of_algebraMap_eq' rfl

/-- Relative divided-power one-forms of a polynomial envelope. -/
abbrev forms :=
  dividedPowerDifferential (E.toD.comp (algebraMap A (MvPolynomial ι A))) E.D.dividedPowers

/-- Polynomial differential coordinates for the algebra selected by its canonical ring map. -/
private def polynomialBasis :
    -- Local instance justification (defeq pin): use the ring-map-selected polynomial algebra appearing in the envelope differential comparison.
    letI : Algebra A (MvPolynomial ι A) := (algebraMap A (MvPolynomial ι A)).toAlgebra
    Module.Basis ι (MvPolynomial ι A) (KaehlerDifferential A (MvPolynomial ι A)) :=
  Eq.ndrec (motive := fun alg : Algebra A (MvPolynomial ι A) ↦
      -- Local instance justification (defeq pin): transport the basis along the equality of the polynomial algebra records inside the dependent motive.
      letI := alg
      Module.Basis ι (MvPolynomial ι A) (KaehlerDifferential A (MvPolynomial ι A)))
    (KaehlerDifferential.mvPolynomialBasis A ι) toAlgebra_algebraMap.symm

set_option backward.privateInPublic true in
/-- The polynomial differentials form a basis before completion. -/
def basis : Module.Basis ι E.D (forms E) :=
  -- Local instance justification (defeq pin): differentialComparison uses the algebra selected by the canonical polynomial ring homomorphism, rather than the original algebra record.
  letI : Algebra A (MvPolynomial ι A) := (algebraMap A (MvPolynomial ι A)).toAlgebra
  -- Local instance justification (noncanonical choice): base change of polynomial differentials uses the action selected by E.toD.
  letI := polynomialAlgebra E
  -- Local instance justification (noncanonical choice): differentialComparison uses the composite coefficient action selected by E.toD.
  letI := baseAlgebra E
  -- Local instance justification (defeq pin): the basis base change and differentialComparison use the same composite scalar tower.
  letI := baseTower E
  ((polynomialBasis (A := A) (ι := ι)).baseChange E.D).map
    (LinearEquiv.ofBijective (differentialComparison E)
      (differentialComparison_bijective γ (algebraMap A (MvPolynomial ι A)) hIJ E hE))

/-- The polynomial-envelope basis vector is the differential of its variable. -/
theorem basis_apply (i : ι) :
    basis E hE i =
      dividedPowerDifferentialDerivation
        (E.toD.comp (algebraMap A (MvPolynomial ι A))) E.D.dividedPowers
        (E.toD (MvPolynomial.X i)) := sorry

/-- The principal-adic completion of the envelope ring. -/
abbrev completedRing (p : ℕ) := AdicCompletion (AdicCompletion.principalIdeal E.D p) E.D

/-- Completed relative forms of the uncompleted envelope. -/
abbrev completedForms (p : ℕ) :=
  AdicCompletion (AdicCompletion.principalIdeal E.D p) (forms E)

/-- A completed coordinate is the continuous extension of an algebraic basis coordinate. -/
def completedCoord (p : ℕ) (i : ι) : completedForms E p →ₗ[completedRing E p] completedRing E p :=
  AdicCompletion.map (AdicCompletion.principalIdeal E.D p) ((basis E hE).coord i)

/-- The differential of a polynomial variable in the completed envelope forms. -/
def dX (p : ℕ) (i : ι) : completedForms E p :=
  AdicCompletion.of (AdicCompletion.principalIdeal E.D p) (forms E)
    (dividedPowerDifferentialDerivation
      (E.toD.comp (algebraMap A (MvPolynomial ι A))) E.D.dividedPowers
      (E.toD (MvPolynomial.X i)))

/-- Completed coordinates evaluate variable differentials as Kronecker deltas. -/
theorem completedCoord_dX (p : ℕ) (i : ι) :
    completedCoord E hE p i (dX E p i) = 1 ∧
      ∀ j, i ≠ j → completedCoord E hE p i (dX E p j) = 0 := sorry

/-- All completed coordinates together distinguish completed envelope forms. -/
theorem completedCoord_jointlyInjective (p : ℕ) (ω η : completedForms E p)
    (h : ∀ i, completedCoord E hE p i ω = completedCoord E hE p i η) : ω = η := sorry

variable (p : ℕ) [Fact p.Prime]
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable (N : ℕ) (hN : Ideal.span {(p : E.D)} ^ N ≤ E.D.ideal)

/-- The divided powers on the distinguished ideal of the completed envelope. -/
abbrev completedDividedPowers := DividedPowers.PAdic.envelopeCompletionDividedPowers E N hN

/-- The base map to the completed envelope. -/
def completedBaseMap : A →+* completedRing E p :=
  (algebraMap E.D (completedRing E p)).comp
    (E.toD.comp (algebraMap A (MvPolynomial ι A)))

/-- The coefficient algebra action on the completed envelope. -/
@[implicit_reducible] def completedBaseAlgebra : Algebra A (completedRing E p) :=
  (completedBaseMap E p).toAlgebra

/-- Algebraic divided-power forms on the completed envelope, with their actual coefficient ring. -/
abbrev completedEnvelopeForms : ModuleCat (completedRing E p) :=
  ModuleCat.of (completedRing E p)
    (dividedPowerDifferential (completedBaseMap E p) (completedDividedPowers E p N hN))

/-- The polynomial-coordinate map to algebraic divided-power forms of the completed envelope. -/
private def formsComparison : forms E →ₗ[E.D]
    (ModuleCat.restrictScalars (algebraMap E.D (completedRing E p))).obj
      (completedEnvelopeForms E p N hN) :=
  (basis E hE).constr E.D (fun i ↦
    dividedPowerDifferentialDerivation (completedBaseMap E p)
      (completedDividedPowers E p N hN)
      (algebraMap E.D (completedRing E p) (E.toD (MvPolynomial.X i))))

set_option backward.privateInPublic true in
/-- The additive comparison between completed forms before and after completing the envelope. -/
def completedFormsComparison : completedForms E p →+
    AdicCompletion (AdicCompletion.principalIdeal (completedRing E p) p)
      (completedEnvelopeForms E p N hN) :=
  AdicCompletion.completeAddMap E.D (completedRing E p) p
    (formsComparison E hE p N hN).toAddMonoidHom

/-- The completed forms comparison respects every scalar in the completed envelope. -/
theorem completedFormsComparison_smul (r : completedRing E p) (ω : completedForms E p) :
    completedFormsComparison E hE p N hN (r • ω) =
      r • completedFormsComparison E hE p N hN ω := sorry

/-- The completed forms comparison bundled over the completed envelope. -/
def completedFormsComparisonLinear : completedForms E p →ₗ[completedRing E p]
    AdicCompletion (AdicCompletion.principalIdeal (completedRing E p) p)
      (completedEnvelopeForms E p N hN) where
  __ := completedFormsComparison E hE p N hN
  map_smul' := completedFormsComparison_smul E hE p N hN

/-- Completing the envelope does not change its completed divided-power forms. -/
theorem completedFormsComparison_bijective :
    Function.Bijective (completedFormsComparison E hE p N hN) := sorry

/-- The canonical linear equivalence of the two completed differential models. -/
def completedFormsEquiv : completedForms E p ≃ₗ[completedRing E p]
    AdicCompletion (AdicCompletion.principalIdeal (completedRing E p) p)
      (completedEnvelopeForms E p N hN) :=
  LinearEquiv.ofBijective (completedFormsComparisonLinear E hE p N hN)
    (completedFormsComparison_bijective E hE p N hN)

/-- The completed comparison takes the continuous universal derivative to the completed
divided-power derivative of the completed ring. -/
theorem completedFormsComparison_derivation (r : completedRing E p) :
    -- Local instance justification (noncanonical choice): the derivative is linear over the coefficient action selected by the explicit envelope.
    letI := baseAlgebra E
    completedFormsComparison E hE p N hN
        (AdicCompletion.completeAddMap E.D E.D p
          (dividedPowerDifferentialDerivation
            (E.toD.comp (algebraMap A (MvPolynomial ι A)))
            E.D.dividedPowers).toLinearMap.toAddMonoidHom r) =
      AdicCompletion.of (AdicCompletion.principalIdeal (completedRing E p) p)
        (completedEnvelopeForms E p N hN)
        (dividedPowerDifferentialDerivation (completedBaseMap E p)
          (completedDividedPowers E p N hN) r) := sorry

end DividedPowerEnvelope.Coordinates
