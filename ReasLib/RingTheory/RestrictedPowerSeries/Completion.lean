/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Polynomial.Quotient
public import ReasLib.RingTheory.RestrictedPowerSeries
public import ReasLib.RingTheory.AdicCompletion.Polynomial
public import ReasLib.RingTheory.Topology.Adic.Complete

/-! # Restricted power series and ideal-adic polynomial completion -/

@[expose] public section

open TopologicalRing
open TopologicalRing.Ideal

noncomputable section

universe u

namespace RestrictedPowerSeries

variable {A : Type u} [CommRing A] [TopologicalSpace A]

variable (ι : Type u) (I : Ideal A)

/-- The least power of an ideal of definition contained in a given open ideal. -/
private def powIndex (hI : IsIdealOfDefinition I) (J : OpenIdeal A) : ℕ :=
  by
    classical
    exact Nat.find (hI.2 (J.1 : Set A) (J.2.mem_nhds J.1.zero_mem))

/-- The least cofinal exponent gives containment in the specified open ideal. -/
private theorem powIndex_le (hI : IsIdealOfDefinition I) (J : OpenIdeal A) :
    I ^ powIndex I hI J ≤ J.1 :=
  by
    classical
    exact Nat.find_spec (hI.2 (J.1 : Set A) (J.2.mem_nhds J.1.zero_mem))

section Components

variable [IsTopologicalRing A] [IsLinearTopology A A]

/-- Evaluation at an open ideal as an algebra map over the coefficient ring. -/
def componentAlgHom (J : OpenIdeal A) :
    RestrictedPowerSeries ι A →ₐ[A] MvPolynomial ι (A ⧸ J.1) where
  __ := component J
  commutes' := sorry

/-- The component algebra map evaluates the underlying component family. -/
theorem componentAlgHom_apply (J : OpenIdeal A) (f : RestrictedPowerSeries ι A) :
    componentAlgHom ι J f = component J f := rfl

end Components

variable [IsAdicRing A]

/-- A power of an ideal of definition, bundled as an open ideal. -/
private def openPow (hI : IsIdealOfDefinition I) (n : ℕ) : OpenIdeal A :=
  ⟨I ^ n, (isAdic_iff.mp hI.isAdic).1 n⟩

/-- The finite-stage map from restricted power series to a polynomial quotient. -/
private def toAdicStage (hI : IsIdealOfDefinition I) (n : ℕ) :
    RestrictedPowerSeries ι A →ₐ[A]
      MvPolynomial ι A ⧸ (I.map (algebraMap A (MvPolynomial ι A))) ^ n :=
  (Ideal.quotientEquivAlgOfEq A
      (Ideal.map_pow (algebraMap A (MvPolynomial ι A)) I n)).toAlgHom.comp
    ((MvPolynomial.quotientEquivQuotientMvPolynomial (σ := ι) (I ^ n)).toAlgHom.comp
      (componentAlgHom ι (openPow I hI n)))

/-- Finite-stage comparison maps commute with adic transition maps. -/
private theorem toAdicStage_compatible (hI : IsIdealOfDefinition I) {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hle)).comp
      (toAdicStage ι I hI n) =
      toAdicStage ι I hI m := sorry

/-- The canonical stagewise algebra map to the ideal-adic polynomial completion. -/
@[no_expose] def toAdicAlgHom (hI : IsIdealOfDefinition I) :
    RestrictedPowerSeries ι A →ₐ[A] IAdicRestrictedPowerSeries ι I :=
  AdicCompletion.liftAlgHom (I.map (algebraMap A (MvPolynomial ι A)))
    (toAdicStage ι I hI) (toAdicStage_compatible ι I hI)

/-- Evaluation of the comparison at an adic stage is its finite-stage map. -/
private theorem eval_toAdicAlgHom (hI : IsIdealOfDefinition I) (n : ℕ)
    (f : RestrictedPowerSeries ι A) :
    AdicCompletion.evalₐ (I.map (algebraMap A (MvPolynomial ι A))) n
        (toAdicAlgHom ι I hI f) =
      toAdicStage ι I hI n f := sorry

/-- The cofinal component family of a completed polynomial is compatible. -/
private theorem ofAdic_compatible (hI : IsIdealOfDefinition I)
    (F : IAdicRestrictedPowerSeries ι I) :
    Compatible fun J : OpenIdeal A ↦
      MvPolynomial.map (Ideal.Quotient.factor (powIndex_le I hI J))
        (IAdicRestrictedPowerSeries.stageHom ι I (powIndex I hI J) F) := sorry

/-- The restricted series whose open-ideal components are the cofinal polynomial stages. -/
private def ofAdic (hI : IsIdealOfDefinition I) (F : IAdicRestrictedPowerSeries ι I) :
    RestrictedPowerSeries ι A :=
  ⟨fun J ↦
    MvPolynomial.map (Ideal.Quotient.factor (powIndex_le I hI J))
      (IAdicRestrictedPowerSeries.stageHom ι I (powIndex I hI J) F),
    ofAdic_compatible ι I hI F⟩

/-- The components of the inverse comparison are the cofinal polynomial stages. -/
private theorem ofAdic_component (hI : IsIdealOfDefinition I)
    (F : IAdicRestrictedPowerSeries ι I) (J : OpenIdeal A) :
    component J (ofAdic ι I hI F) =
      MvPolynomial.map (Ideal.Quotient.factor (powIndex_le I hI J))
        (IAdicRestrictedPowerSeries.stageHom ι I (powIndex I hI J) F) := rfl

/-- The algebra map from the polynomial completion to restricted power series. -/
@[no_expose] def ofAdicAlgHom (hI : IsIdealOfDefinition I) :
    IAdicRestrictedPowerSeries ι I →ₐ[A] RestrictedPowerSeries ι A where
  toFun := ofAdic ι I hI
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry
  commutes' := sorry

/-- The inverse algebra map has the specified cofinal component family. -/
private theorem ofAdicAlgHom_apply (hI : IsIdealOfDefinition I)
    (F : IAdicRestrictedPowerSeries ι I) :
    ofAdicAlgHom ι I hI F = ofAdic ι I hI F := rfl

/-- Restricted power series are canonically equivalent to the polynomial
completion along an ideal of definition. -/
def adicEquiv (hI : IsIdealOfDefinition I) :
    RestrictedPowerSeries ι A ≃ₐ[A] IAdicRestrictedPowerSeries ι I :=
  AlgEquiv.ofAlgHom (toAdicAlgHom ι I hI) (ofAdicAlgHom ι I hI) sorry sorry

/-- The canonical equivalence sends a restricted polynomial to its completion. -/
theorem adicEquiv_ofPolynomial (hI : IsIdealOfDefinition I) (g : MvPolynomial ι A) :
    adicEquiv ι I hI (ofPolynomial g) =
      AdicCompletion.of (I.map (algebraMap A (MvPolynomial ι A))) (MvPolynomial ι A) g := sorry

/-- The canonical equivalence sends restricted variables to completed variables. -/
theorem adicEquiv_X (hI : IsIdealOfDefinition I) (i : ι) :
    adicEquiv ι I hI (ofPolynomial (MvPolynomial.X i)) =
      AdicCompletion.of (I.map (algebraMap A (MvPolynomial ι A)))
        (MvPolynomial ι A) (MvPolynomial.X i) :=
  adicEquiv_ofPolynomial ι I hI (MvPolynomial.X i)

end RestrictedPowerSeries
