/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DividedPowers.Envelope.Coordinates
public import ReasLib.RingTheory.Kaehler.DeRham.Connection.Adic.QuasiNilpotent
public import ReasLib.AlgebraicGeometry.Crystalline.Completed.Geometry
public import ReasLib.AlgebraicGeometry.Crystalline.Connection
public import ReasLib.RingTheory.DividedPowers.Envelope.Crystalline
public import ReasLib.RingTheory.AdicCompletion.Filtration
public import ReasLib.Algebra.Module.IdealPower.Quotient.Hom

@[expose] public section

set_option maxHeartbeats 1600000
set_option backward.privateInPublic true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Crystalline
open KaehlerDifferential.DeRham DividedPowers.PAdic
open scoped TensorProduct

universe u

namespace CrystallineModuleSheaf.CrisModuleSheaf.Completed

variable (p : ℕ) [Fact p.Prime]
variable {A C ι : Type u} [CommRing A] [CommRing C] [Algebra A C]
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable {I : Ideal A} (γ : DividedPowers I)
variable (π : MvPolynomial ι A →ₐ[A] C) (hπ : Function.Surjective π)
variable {J : Ideal (MvPolynomial ι A)} (hJ : J = RingHom.ker π.toRingHom)
variable (hIC : Ideal.map (algebraMap A C) I = ⊥) (hpnil : IsNilpotent (p : C))
variable {hIJ : Ideal.map (algebraMap A (MvPolynomial ι A)) I ≤ J}
variable (E : DividedPowerEnvelope I γ (algebraMap A (MvPolynomial ι A)) J hIJ)
variable (hE : DividedPowerEnvelope.IsUniversal γ (algebraMap A (MvPolynomial ι A)) hIJ E)

/-- A nilpotence-derived bound for extending the envelope divided powers to its completion. -/
private def envelopeBound : ℕ :=
  (pAdicCompletionIsCrisWedgeObject p A (MvPolynomial ι A) I γ C (algebraMap A C)
    π.toRingHom π.comp_algebraMap hIC J hJ hπ hpnil E hE).choose

/-- The bound places the required power of `p` in the distinguished envelope ideal. -/
private def envelopeContainment :
    Ideal.span {(p : E.D)} ^ envelopeBound p γ π hπ hJ hIC hpnil E hE ≤ E.D.ideal :=
  (pAdicCompletionIsCrisWedgeObject p A (MvPolynomial ι A) I γ C (algebraMap A C)
    π.toRingHom π.comp_algebraMap hIC J hJ hπ hpnil E hE).choose_spec.2.choose

/-- The completed crystalline object of the universal polynomial envelope, with its
canonical extended divided powers and quotient onto the presented algebra. -/
def envelopeObject :=
  let N := envelopeBound p γ π hπ hJ hIC hpnil E hE
  let hN := envelopeContainment p γ π hπ hJ hIC hpnil E hE
  envelopeCompletedCrisObject p γ (algebraMap A C) π.toRingHom hπ π.comp_algebraMap
    hIC hpnil hJ E hE N hN (envelopeCompletionDividedPowers E N hN)
    (envelopeCompletionDividedPowers_isDPMorphism E N hN)

variable {X : Scheme.{u}} (IS : (Spec (.of A)).IdealSheafData)
variable (γS : ∀ V : (Spec (.of A)).affineOpens, DividedPowers (IS.ideal V))
variable (hc : ∀ (V : (Spec (.of A)).affineOpens) (f : Γ(Spec (.of A), V)),
  (γS V).IsDPMorphism (γS ((Spec (.of A)).affineBasicOpen f))
    ((Spec (.of A)).presheaf.map (homOfLE ((Spec (.of A)).basicOpen_le f)).op).hom)
variable (x₀ : X ⟶ IS.subscheme) (eX : Spec (.of C) ≅ X)
variable (heX : eX.hom ≫ x₀ ≫ IS.subschemeι = Spec.map (CommRingCat.ofHom (algebraMap A C)))
variable (hI : IS = DividedPowers.affineIdeal (I := I))
variable (hγ : DividedPowers.IsDPMorphism γ
  (γS ⟨⊤, isAffineOpen_top (Spec (.of A))⟩) (Scheme.ΓSpecIso (.of A)).inv.hom)

/-- The actual geometric quotient thickenings of the completed polynomial envelope. -/
abbrev stages :=
  CechCrisCover.completedSmallSystem γ hIC hpnil IS γS hc x₀ eX.hom heX hI hγ
    inferInstance (envelopeObject p γ π hπ hJ hIC hpnil E hE)

/-- The inverse system of crystalline coefficient modules on the actual quotient thickenings. -/
abbrev coefficientSystem (F : CrisModuleSheaf (Spec (.of A)) IS γS hc X x₀) :=
  CechCrisCover.completedModuleSystem γ hIC hpnil IS γS hc x₀ eX.hom heX hI hγ
    inferInstance (envelopeObject p γ π hπ hJ hIC hpnil E hE) F

/-- The inverse limit of sections of a crystalline module on the completed envelope stages. -/
abbrev coefficientModule (F : CrisModuleSheaf (Spec (.of A)) IS γS hc X x₀) :=
  CechCrisCover.completedCoefficientModule γ hIC hpnil IS γS hc x₀ eX.hom heX hI hγ
    inferInstance (envelopeObject p γ π hπ hJ hIC hpnil E hE) F


/-- The actual ring of a quotient thickening, including the crystalline tail offset. -/
abbrev stageRing (e : ℕ) :=
  pAdicQuotientRing γ (algebraMap A C) hIC hpnil (envelopeObject p γ π hπ hJ hIC hpnil E hE) e

/-- The exponent of the power of `p` defining a geometric stage. -/
abbrev stageExponent (e : ℕ) :=
  pAdicExponent γ (algebraMap A C) hIC hpnil (envelopeObject p γ π hπ hJ hIC hpnil E hE) e

/-- The quotient map from the completed envelope to an actual geometric stage ring. -/
abbrev stageRingMap (e : ℕ) :
    DividedPowerEnvelope.Coordinates.completedRing E p →+* stageRing p γ π hπ hJ hIC hpnil E hE e :=
  (pAdicQuotientMk γ (algebraMap A C) hIC hpnil (envelopeObject p γ π hπ hJ hIC hpnil E hE) e).toRingHom

/-- The divided-power base map at a geometric stage. -/
abbrev stageBaseMap (e : ℕ) : A →+* stageRing p γ π hπ hJ hIC hpnil E hE e :=
  (pAdicQuotientThickening γ (algebraMap A C) hIC hpnil (envelopeObject p γ π hπ hJ hIC hpnil E hE) e).base.toRingHom

/-- The completed-envelope algebra action on the quotient stage. -/
@[implicit_reducible] def stageAlgebra (e : ℕ) :
    Algebra (DividedPowerEnvelope.Coordinates.completedRing E p) (stageRing p γ π hπ hJ hIC hpnil E hE e) :=
  (stageRingMap p γ π hπ hJ hIC hpnil E hE e).toAlgebra

/-- The base algebra action on an actual quotient stage. -/
@[implicit_reducible] def stageBaseAlgebra (e : ℕ) : Algebra A (stageRing p γ π hπ hJ hIC hpnil E hE e) :=
  (stageBaseMap p γ π hπ hJ hIC hpnil E hE e).toAlgebra

/-- The quotient-stage base action factors through the completed envelope. -/
@[implicit_reducible] def stageTower (e : ℕ) :
    -- Local instance justification (noncanonical choice): the relative completed derivative uses the envelope's explicit structural map.
    letI := DividedPowerEnvelope.Coordinates.completedBaseAlgebra E p
    -- Local instance justification (noncanonical choice): the geometric quotient map selects the completed-envelope action on this stage.
    letI := stageAlgebra p γ π hπ hJ hIC hpnil E hE e
    -- Local instance justification (noncanonical choice): the geometric stage base map selects its coefficient action.
    letI := stageBaseAlgebra p γ π hπ hJ hIC hpnil E hE e
    IsScalarTower A (DividedPowerEnvelope.Coordinates.completedRing E p) (stageRing p γ π hπ hJ hIC hpnil E hE e) :=
  -- Local instance justification (noncanonical choice): the relative completed derivative uses the envelope's explicit structural map.
  letI := DividedPowerEnvelope.Coordinates.completedBaseAlgebra E p
  -- Local instance justification (noncanonical choice): the geometric quotient map selects the completed-envelope action on this stage.
  letI := stageAlgebra p γ π hπ hJ hIC hpnil E hE e
  -- Local instance justification (noncanonical choice): the geometric stage base map selects its coefficient action.
  letI := stageBaseAlgebra p γ π hπ hJ hIC hpnil E hE e
  IsScalarTower.of_algebraMap_eq' (congrArg (fun f : A →+* E.D ↦
    (stageRingMap p γ π hπ hJ hIC hpnil E hE e).comp
      ((algebraMap E.D (DividedPowerEnvelope.Coordinates.completedRing E p)).comp f)) E.base_toD)

/-- Affine global sections of the geometric divided-power differential sheaf at a stage. -/
private abbrev affineStageForms (e : ℕ) : ModuleCat (stageRing p γ π hπ hJ hIC hpnil E hE e) :=
  (moduleSpecΓFunctor (R := .of (stageRing p γ π hπ hJ hIC hpnil E hE e))).obj
    (CrystallineObject.DividedPowerFirstOrderThickening.differentials ((stages p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ).obj e)).module

/-- Geometric stage one-forms, with scalars restricted from the completed envelope. -/
abbrev stageForms (e : ℕ) : ModuleCat (DividedPowerEnvelope.Coordinates.completedRing E p) :=
  (ModuleCat.restrictScalars (stageRingMap p γ π hπ hJ hIC hpnil E hE e)).obj (affineStageForms p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ e)

/-- The completed-envelope action on affine differential sections is quotient restriction. -/
@[implicit_reducible] private def affineStageFormsModule (e : ℕ) :
    Module (DividedPowerEnvelope.Coordinates.completedRing E p) (affineStageForms p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ e) :=
  Module.compHom _ (stageRingMap p γ π hπ hJ hIC hpnil E hE e)

/-- The two scalar actions on geometric differential sections form a tower. -/
@[implicit_reducible] private def affineStageFormsTower (e : ℕ) :
    -- Local instance justification (noncanonical choice): the geometric quotient map selects the completed-envelope action on this stage.
    letI := stageAlgebra p γ π hπ hJ hIC hpnil E hE e
    -- Local instance justification (defeq pin): the geometric differential sections use the same quotient restriction as stageForms.
    letI := affineStageFormsModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ e
    IsScalarTower (DividedPowerEnvelope.Coordinates.completedRing E p)
      (stageRing p γ π hπ hJ hIC hpnil E hE e) (affineStageForms p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ e) :=
  -- Local instance justification (noncanonical choice): the geometric quotient map selects the completed-envelope action on this stage.
  letI := stageAlgebra p γ π hπ hJ hIC hpnil E hE e
  -- Local instance justification (defeq pin): the geometric differential sections use the same quotient restriction as stageForms.
  letI := affineStageFormsModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ e
  IsScalarTower.of_compHom _ _ _

/-- The base action on affine differential sections is restriction along the stage base. -/
@[implicit_reducible] private def affineStageFormsBaseModule (e : ℕ) :
    Module A (affineStageForms p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ e) :=
  Module.compHom _ (stageBaseMap p γ π hπ hJ hIC hpnil E hE e)

/-- Base and stage scalars act compatibly on geometric differential sections. -/
@[implicit_reducible] private def affineStageFormsBaseTower (e : ℕ) :
    -- Local instance justification (noncanonical choice): the geometric stage base map selects its coefficient action.
    letI := stageBaseAlgebra p γ π hπ hJ hIC hpnil E hE e
    -- Local instance justification (noncanonical choice): the relative geometric derivative uses the stage base-map restriction on its sections.
    letI := affineStageFormsBaseModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ e
    IsScalarTower A (stageRing p γ π hπ hJ hIC hpnil E hE e)
      (affineStageForms p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ e) :=
  -- Local instance justification (noncanonical choice): the geometric stage base map selects its coefficient action.
  letI := stageBaseAlgebra p γ π hπ hJ hIC hpnil E hE e
  -- Local instance justification (noncanonical choice): the relative geometric derivative uses the stage base-map restriction on its sections.
  letI := affineStageFormsBaseModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ e
  IsScalarTower.of_compHom _ _ _

/-- The base action on geometric forms factors through the completed envelope. -/
@[implicit_reducible] private def affineStageFormsCompletedTower (e : ℕ) :
    -- Local instance justification (noncanonical choice): the relative completed derivative uses the envelope's explicit structural map.
    letI := DividedPowerEnvelope.Coordinates.completedBaseAlgebra E p
    -- Local instance justification (noncanonical choice): the geometric quotient map selects the completed-envelope action on this stage.
    letI := stageAlgebra p γ π hπ hJ hIC hpnil E hE e
    -- Local instance justification (noncanonical choice): the geometric stage base map selects its coefficient action.
    letI := stageBaseAlgebra p γ π hπ hJ hIC hpnil E hE e
    -- Local instance justification (defeq pin): the two explicit stage actions have the composite structural map required by the derivative.
    letI := stageTower p γ π hπ hJ hIC hpnil E hE e
    -- Local instance justification (defeq pin): the geometric differential sections use the same quotient restriction as stageForms.
    letI := affineStageFormsModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ e
    -- Local instance justification (noncanonical choice): the relative geometric derivative uses the stage base-map restriction on its sections.
    letI := affineStageFormsBaseModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ e
    IsScalarTower A (DividedPowerEnvelope.Coordinates.completedRing E p)
      (affineStageForms p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ e) :=
  -- Local instance justification (noncanonical choice): the relative completed derivative uses the envelope's explicit structural map.
  letI := DividedPowerEnvelope.Coordinates.completedBaseAlgebra E p
  -- Local instance justification (noncanonical choice): the geometric quotient map selects the completed-envelope action on this stage.
  letI := stageAlgebra p γ π hπ hJ hIC hpnil E hE e
  -- Local instance justification (noncanonical choice): the geometric stage base map selects its coefficient action.
  letI := stageBaseAlgebra p γ π hπ hJ hIC hpnil E hE e
  -- Local instance justification (defeq pin): the two explicit stage actions have the composite structural map required by the derivative.
  letI := stageTower p γ π hπ hJ hIC hpnil E hE e
  -- Local instance justification (defeq pin): the geometric differential sections use the same quotient restriction as stageForms.
  letI := affineStageFormsModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ e
  -- Local instance justification (noncanonical choice): the relative geometric derivative uses the stage base-map restriction on its sections.
  letI := affineStageFormsBaseModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ e
  IsScalarTower.of_algebraMap_smul (fun a m ↦
    congrArg (fun q : stageRing p γ π hπ hJ hIC hpnil E hE e ↦ q • m)
      (RingHom.congr_fun (IsScalarTower.algebraMap_eq A
        (DividedPowerEnvelope.Coordinates.completedRing E p)
        (stageRing p γ π hπ hJ hIC hpnil E hE e)).symm a))

/-- The universal geometric divided-power derivative on affine quotient-stage sections. -/
private def stageDerivation (e : ℕ) :
    (affineStageForms p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ e).Derivation (CommRingCat.ofHom (stageBaseMap p γ π hπ hJ hIC hpnil E hE e)) :=
  Scheme.Modules.AffineDerivation.globalSections (CommRingCat.ofHom (stageBaseMap p γ π hπ hJ hIC hpnil E hE e))
    (CrystallineObject.DividedPowerFirstOrderThickening.differentials ((stages p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ).obj e)).module
    (universalDerivation ((stages p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ).obj e))

/-- Pull the affine geometric derivative back along the actual completed-envelope quotient. -/
private def stageKaehlerComparison (e : ℕ) :
    -- Local instance justification (noncanonical choice): the relative completed derivative uses the envelope's explicit structural map.
    letI := DividedPowerEnvelope.Coordinates.completedBaseAlgebra E p
    KaehlerDifferential A (DividedPowerEnvelope.Coordinates.completedRing E p) →ₗ[
      DividedPowerEnvelope.Coordinates.completedRing E p] stageForms p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ e :=
  -- Local instance justification (noncanonical choice): the relative completed derivative uses the envelope's explicit structural map.
  letI := DividedPowerEnvelope.Coordinates.completedBaseAlgebra E p
  -- Local instance justification (noncanonical choice): the geometric quotient map selects the completed-envelope action on this stage.
  letI := stageAlgebra p γ π hπ hJ hIC hpnil E hE e
  -- Local instance justification (noncanonical choice): the geometric stage base map selects its coefficient action.
  letI := stageBaseAlgebra p γ π hπ hJ hIC hpnil E hE e
  -- Local instance justification (defeq pin): the two explicit stage actions have the composite structural map required by the derivative.
  letI := stageTower p γ π hπ hJ hIC hpnil E hE e
  -- Local instance justification (defeq pin): the geometric differential sections use the same quotient restriction as stageForms.
  letI := affineStageFormsModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ e
  -- Local instance justification (noncanonical choice): the relative geometric derivative uses the stage base-map restriction on its sections.
  letI := affineStageFormsBaseModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ e
  -- Local instance justification (defeq pin): the quotient-restricted action on differential sections factors through the stage ring.
  letI := affineStageFormsTower p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ e
  -- Local instance justification (defeq pin): the selected base restriction on geometric forms factors through the stage ring.
  letI := affineStageFormsBaseTower p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ e
  -- Local instance justification (defeq pin): the relative derivative requires compatibility of the two selected restrictions on geometric forms.
  letI := affineStageFormsCompletedTower p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ e
  (Derivation.compAlgebraMap (R := A)
    (B := stageRing p γ π hπ hJ hIC hpnil E hE e)
    (M := affineStageForms p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ e)
    (DividedPowerEnvelope.Coordinates.completedRing E p)
    (stageDerivation p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ e)).liftKaehlerDifferential

/-- The geometric stage derivative annihilates the completed envelope's divided-power relations. -/
theorem stageDifferentialComparison_relations (e : ℕ) :
    dividedPowerRelations (DividedPowerEnvelope.Coordinates.completedBaseMap E p)
        (DividedPowerEnvelope.Coordinates.completedDividedPowers E p
          (envelopeBound p γ π hπ hJ hIC hpnil E hE) (envelopeContainment p γ π hπ hJ hIC hpnil E hE)) ≤
      LinearMap.ker (stageKaehlerComparison p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ e) := sorry

/-- The differential comparison descended through the divided-power relations. -/
private def stageFormsComparison (e : ℕ) :
    DividedPowerEnvelope.Coordinates.completedEnvelopeForms E p
        (envelopeBound p γ π hπ hJ hIC hpnil E hE) (envelopeContainment p γ π hπ hJ hIC hpnil E hE) →ₗ[
      DividedPowerEnvelope.Coordinates.completedRing E p] stageForms p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ e :=
  (dividedPowerRelations (DividedPowerEnvelope.Coordinates.completedBaseMap E p)
    (DividedPowerEnvelope.Coordinates.completedDividedPowers E p
      (envelopeBound p γ π hπ hJ hIC hpnil E hE) (envelopeContainment p γ π hπ hJ hIC hpnil E hE))).liftQ
    (stageKaehlerComparison p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ e) (stageDifferentialComparison_relations p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ e)

/-- The geometric differential comparison kills the power defining its actual quotient stage. -/
theorem stageDifferentialComparison_killsPower (e : ℕ) :
    AdicCompletion.principalIdeal (DividedPowerEnvelope.Coordinates.completedRing E p) p ^
        stageExponent p γ π hπ hJ hIC hpnil E hE e •
        (⊤ : Submodule (DividedPowerEnvelope.Coordinates.completedRing E p)
          (DividedPowerEnvelope.Coordinates.completedEnvelopeForms E p
            (envelopeBound p γ π hπ hJ hIC hpnil E hE) (envelopeContainment p γ π hπ hJ hIC hpnil E hE))) ≤
      LinearMap.ker (stageFormsComparison p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ e) := sorry

/-- The finite-stage differential comparison descends through the actual power quotient. -/
private def differentialQuotientComparison (e : ℕ) :=
  (AdicCompletion.principalIdeal (DividedPowerEnvelope.Coordinates.completedRing E p) p ^
    stageExponent p γ π hπ hJ hIC hpnil E hE e •
      (⊤ : Submodule (DividedPowerEnvelope.Coordinates.completedRing E p)
        (DividedPowerEnvelope.Coordinates.completedEnvelopeForms E p
          (envelopeBound p γ π hπ hJ hIC hpnil E hE) (envelopeContainment p γ π hπ hJ hIC hpnil E hE)))).liftQ
    (stageFormsComparison p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ e) (stageDifferentialComparison_killsPower p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ e)

/-- The comparison from completed envelope forms to geometric stage differential sections. -/
def stageDifferentialComparison (e : ℕ) :
    DividedPowerEnvelope.Coordinates.completedForms E p →ₗ[
      DividedPowerEnvelope.Coordinates.completedRing E p] stageForms p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ e :=
  (differentialQuotientComparison p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ e).comp
    ((AdicCompletion.eval (AdicCompletion.principalIdeal
        (DividedPowerEnvelope.Coordinates.completedRing E p) p)
      (DividedPowerEnvelope.Coordinates.completedEnvelopeForms E p
        (envelopeBound p γ π hπ hJ hIC hpnil E hE) (envelopeContainment p γ π hπ hJ hIC hpnil E hE)) (stageExponent p γ π hπ hJ hIC hpnil E hE e)).comp
      (DividedPowerEnvelope.Coordinates.completedFormsComparisonLinear E hE p
        (envelopeBound p γ π hπ hJ hIC hpnil E hE) (envelopeContainment p γ π hπ hJ hIC hpnil E hE)))

/-- The finite-stage comparison has the universal geometric derivative, with the canonical sign. -/
theorem stageDifferentialComparison_derivation (e : ℕ)
    (r : DividedPowerEnvelope.Coordinates.completedRing E p) :
    -- Local instance justification (noncanonical choice): the relative connection uses the coefficient action selected by the explicit polynomial envelope.
    letI := DividedPowerEnvelope.Coordinates.baseAlgebra E
    stageDifferentialComparison p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ e
        (DPPolynomial.DeRham.completedDerivation A E.D E.D.dividedPowers p r) =
      (stageDerivation p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ e).d (stageRingMap p γ π hπ hJ hIC hpnil E hE e r) := sorry

/-- The actual geometric pullback map on differential sections between consecutive stages. -/
private def stageFormsStep (e : ℕ) :
    AddCommGrpCat.of (stageForms p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ (e + 1)) ⟶ AddCommGrpCat.of (stageForms p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ e) :=
  abelianGlobalSections_map ((CechCrisCover.completedSmallStep γ hIC hpnil
      IS γS hc x₀ eX.hom heX hI hγ inferInstance (envelopeObject p γ π hπ hJ hIC hpnil E hE) e).hom.thickening)
    (differentialsPullback (CechCrisCover.completedSmallStep γ hIC hpnil
      IS γS hc x₀ eX.hom heX hI hγ inferInstance (envelopeObject p γ π hπ hJ hIC hpnil E hE) e))

/-- The inverse system of the actual geometric differential sections. -/
private def stageFormsSystem : ℕᵒᵖ ⥤ AddCommGrpCat :=
  Functor.ofOpSequence (X := fun e ↦ AddCommGrpCat.of (stageForms p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ e)) (stageFormsStep p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ)

/-- Differential comparison commutes with the actual geometric stage transitions. -/
theorem stageDifferentialComparison_naturality {i j : ℕᵒᵖ} (f : i ⟶ j) :
    ((stageFormsSystem p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ).map f).hom.comp
        (stageDifferentialComparison p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ i.unop).toAddMonoidHom =
      (stageDifferentialComparison p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ j.unop).toAddMonoidHom := sorry

/-- At each affine stage the descended differential comparison is bijective. -/
theorem stageDifferentialComparison_bijective (e : ℕ) :
    Function.Bijective (differentialQuotientComparison p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ e) := sorry


variable (F : CrisModuleSheaf (Spec (.of A)) IS γS hc X x₀)

/-- The completed envelope acts on the ring of functions of a quotient thickening. -/
@[implicit_reducible] private def stageSectionsAlgebra (e : ℕ) : Algebra (DividedPowerEnvelope.Coordinates.completedRing E p) Γ(Spec (.of (stageRing p γ π hπ hJ hIC hpnil E hE e)), ⊤) :=
  ((Scheme.ΓSpecIso (.of (stageRing p γ π hπ hJ hIC hpnil E hE e))).inv.hom.comp (stageRingMap p γ π hπ hJ hIC hpnil E hE e)).toAlgebra

/-- The completed-envelope action on sections is restriction along the quotient. -/
@[implicit_reducible] private def stageSectionsModule (e : ℕ) (M : (Spec (.of (stageRing p γ π hπ hJ hIC hpnil E hE e))).Modules) :
    Module (DividedPowerEnvelope.Coordinates.completedRing E p) (M.val.obj (op ⊤)) :=
  Module.compHom _ ((Scheme.ΓSpecIso (.of (stageRing p γ π hπ hJ hIC hpnil E hE e))).inv.hom.comp (stageRingMap p γ π hπ hJ hIC hpnil E hE e))

/-- Stage section scalars factor through the affine function ring. -/
@[implicit_reducible] private def stageSectionsTower (e : ℕ) (M : (Spec (.of (stageRing p γ π hπ hJ hIC hpnil E hE e))).Modules) :
    -- Local instance justification (noncanonical choice): the stage quotient and affine section isomorphism select the action on affine functions.
    letI := stageSectionsAlgebra p γ π hπ hJ hIC hpnil E hE e
    -- Local instance justification (defeq pin): the section module action is restriction along the same affine function map.
    letI := stageSectionsModule p γ π hπ hJ hIC hpnil E hE e M
    IsScalarTower (DividedPowerEnvelope.Coordinates.completedRing E p) Γ(Spec (.of (stageRing p γ π hπ hJ hIC hpnil E hE e)), ⊤) (M.val.obj (op ⊤)) :=
  -- Local instance justification (noncanonical choice): the stage quotient and affine section isomorphism select the action on affine functions.
  letI := stageSectionsAlgebra p γ π hπ hJ hIC hpnil E hE e
  -- Local instance justification (defeq pin): the section module action is restriction along the same affine function map.
  letI := stageSectionsModule p γ π hπ hJ hIC hpnil E hE e M
  IsScalarTower.of_compHom _ _ _

/-- Sections of the geometric tensor of coefficients and differentials at a quotient stage. -/
private abbrev stageTensorSheaf (e : ℕ) :=
  SheafOfModules.RingedSite.moduleTensor (𝒪 := ((stages p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ).obj e).obj.1.thickening.sheaf)
    (F.obj ((stages p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ).obj e)) (CrystallineObject.DividedPowerFirstOrderThickening.differentials ((stages p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ).obj e)).module

/-- Tensor sections at a geometric stage, with their quotient-restricted scalar action. -/
private abbrev stageTensorModule (e : ℕ) : ModuleCat (DividedPowerEnvelope.Coordinates.completedRing E p) :=
  (ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of (stageRing p γ π hπ hJ hIC hpnil E hE e))).inv.hom.comp
    (stageRingMap p γ π hπ hJ hIC hpnil E hE e))).obj ((stageTensorSheaf p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F e).val.obj (op ⊤))

/-- The bilinear pure-tensor map on geometric quotient-stage sections. -/
private def stageTensorBilinear (e : ℕ) :
    (coefficientSystem p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F).obj (op e) →ₗ[(DividedPowerEnvelope.Coordinates.completedRing E p)]
      stageForms p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ e →ₗ[(DividedPowerEnvelope.Coordinates.completedRing E p)] stageTensorModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F e :=
  -- Local instance justification (defeq pin): pure-tensor sections use their native function-ring modules, while the inputs specify their quotient-restricted actions.
  letI := stageSectionsAlgebra p γ π hπ hJ hIC hpnil E hE e
  -- Local instance justification (defeq pin): pin the coefficient-section restriction.
  letI := stageSectionsModule p γ π hπ hJ hIC hpnil E hE e (F.obj ((stages p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ).obj e))
  -- Local instance justification (defeq pin): pin the differential-section restriction.
  letI := stageSectionsModule p γ π hπ hJ hIC hpnil E hE e
    (CrystallineObject.DividedPowerFirstOrderThickening.differentials ((stages p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ).obj e)).module
  -- Local instance justification (defeq pin): pin the tensor-section restriction.
  letI := stageSectionsModule p γ π hπ hJ hIC hpnil E hE e (stageTensorSheaf p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F e)
  -- Local instance justification (defeq pin): the coefficient restriction factors through functions.
  letI := stageSectionsTower p γ π hπ hJ hIC hpnil E hE e (F.obj ((stages p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ).obj e))
  -- Local instance justification (defeq pin): the differential restriction factors through functions.
  letI := stageSectionsTower p γ π hπ hJ hIC hpnil E hE e
    (CrystallineObject.DividedPowerFirstOrderThickening.differentials ((stages p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ).obj e)).module
  -- Local instance justification (defeq pin): the tensor restriction factors through functions.
  letI := stageSectionsTower p γ π hπ hJ hIC hpnil E hE e (stageTensorSheaf p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F e)
  (SheafOfModules.RingedSite.tensorSectionLinear ((stages p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ).obj e).obj.1.thickening.sheaf
    (F.obj ((stages p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ).obj e)) (CrystallineObject.DividedPowerFirstOrderThickening.differentials ((stages p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ).obj e)).module
    (op ⊤)).restrictScalars₁₂ (R := Γ(Spec (.of (stageRing p γ π hπ hJ hIC hpnil E hE e)), ⊤))
      (S := Γ(Spec (.of (stageRing p γ π hπ hJ hIC hpnil E hE e)), ⊤)) (DividedPowerEnvelope.Coordinates.completedRing E p) (DividedPowerEnvelope.Coordinates.completedRing E p)

/-- The tensor comparison combines actual coefficient projections and differential comparison. -/
private def stageTensorLinear (e : ℕ) :
    coefficientModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F ⊗[(DividedPowerEnvelope.Coordinates.completedRing E p)] DividedPowerEnvelope.Coordinates.completedForms E p →ₗ[(DividedPowerEnvelope.Coordinates.completedRing E p)]
      stageTensorModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F e :=
  TensorProduct.lift ((stageTensorBilinear p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F e).compl₁₂
    (limit.π (coefficientSystem p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F) (op e)).hom (stageDifferentialComparison p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ e))

/-- The tensor comparison annihilates the power defining its geometric stage. -/
theorem stageTensorComparison_killsPower (e : ℕ) :
    AdicCompletion.principalIdeal (DividedPowerEnvelope.Coordinates.completedRing E p) p ^ stageExponent p γ π hπ hJ hIC hpnil E hE e •
      (⊤ : Submodule (DividedPowerEnvelope.Coordinates.completedRing E p)
        (coefficientModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F ⊗[(DividedPowerEnvelope.Coordinates.completedRing E p)] DividedPowerEnvelope.Coordinates.completedForms E p)) ≤
      LinearMap.ker (stageTensorLinear p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F e) := sorry

/-- The tensor comparison descended through the power quotient of its actual geometric stage. -/
private def stageTensorComparison (e : ℕ) :=
  (AdicCompletion.principalIdeal (DividedPowerEnvelope.Coordinates.completedRing E p) p ^ stageExponent p γ π hπ hJ hIC hpnil E hE e •
    (⊤ : Submodule (DividedPowerEnvelope.Coordinates.completedRing E p)
      (coefficientModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F ⊗[(DividedPowerEnvelope.Coordinates.completedRing E p)] DividedPowerEnvelope.Coordinates.completedForms E p))).liftQ
    (stageTensorLinear p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F e) (stageTensorComparison_killsPower p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F e)

/-- Pullback on sections of the geometric coefficient-differential tensor between stages. -/
private def stageTensorStep (e : ℕ) :
    AddCommGrpCat.of (stageTensorModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F (e + 1)) ⟶
      AddCommGrpCat.of (stageTensorModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F e) :=
  let f := CechCrisCover.completedSmallStep γ hIC hpnil
    IS γS hc x₀ eX.hom heX hI hγ inferInstance (envelopeObject p γ π hπ hJ hIC hpnil E hE) e
  abelianGlobalSections_map f.hom.thickening
    (schemeModulesTensorComparison f.hom.thickening (F.comparison f) (differentialsPullback f))

/-- The actual inverse system of geometric coefficient-differential tensor sections. -/
private def stageTensorSystem : ℕᵒᵖ ⥤ AddCommGrpCat :=
  Functor.ofOpSequence (X := fun e ↦ AddCommGrpCat.of (stageTensorModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F e))
    (stageTensorStep p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F)

/-- The completed algebraic tensor of the inverse-limit coefficient module and envelope forms. -/
abbrev completedTensor :=
  AdicCompletion (AdicCompletion.principalIdeal (DividedPowerEnvelope.Coordinates.completedRing E p) p)
    (coefficientModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F ⊗[(DividedPowerEnvelope.Coordinates.completedRing E p)] DividedPowerEnvelope.Coordinates.completedForms E p)

/-- Evaluate a completed tensor in the actual geometric quotient tensor sections. -/
private def tensorProjection (e : ℕ) : completedTensor p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F →+ stageTensorModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F e :=
  (stageTensorComparison p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F e).toAddMonoidHom.comp
    (AdicCompletion.eval (AdicCompletion.principalIdeal (DividedPowerEnvelope.Coordinates.completedRing E p) p)
      (coefficientModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F ⊗[(DividedPowerEnvelope.Coordinates.completedRing E p)] DividedPowerEnvelope.Coordinates.completedForms E p)
      (stageExponent p γ π hπ hJ hIC hpnil E hE e)).toAddMonoidHom

/-- Tensor comparison commutes with the actual geometric transition maps. -/
theorem stageTensorComparison_naturality {i j : ℕᵒᵖ} (f : i ⟶ j) :
    AddCommGrpCat.ofHom (tensorProjection p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F i.unop) ≫ (stageTensorSystem p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F).map f =
      AddCommGrpCat.ofHom (tensorProjection p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F j.unop) := sorry


/-- The comparison from the completed algebraic tensor to the inverse limit of geometric tensors. -/
def completedTensorComparison : completedTensor p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F →+ (limit (stageTensorSystem p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F) : AddCommGrpCat) :=
  (limit.lift (stageTensorSystem p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F)
    { pt := AddCommGrpCat.of (completedTensor p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F)
      π :=
        { app := fun i ↦ AddCommGrpCat.ofHom (tensorProjection p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F i.unop)
          naturality := fun i j f ↦ (Category.id_comp _).trans
            (stageTensorComparison_naturality p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F f).symm } }).hom

/-- Projection of the completed tensor comparison is its actual finite-stage comparison. -/
theorem completedTensorComparison_π (e : ℕ) (z : completedTensor p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F) :
    (limit.π (stageTensorSystem p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F) (op e)).hom (completedTensorComparison p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F z) =
      tensorProjection p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F e z := sorry

/-- The coefficient projection descended through the power defining a geometric stage. -/
private def coefficientQuotient (e : ℕ) :=
  (AdicCompletion.principalIdeal (DividedPowerEnvelope.Coordinates.completedRing E p) p ^ stageExponent p γ π hπ hJ hIC hpnil E hE e •
    (⊤ : Submodule (DividedPowerEnvelope.Coordinates.completedRing E p) (coefficientModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F))).liftQ
    (limit.π (coefficientSystem p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F) (op e)).hom
    (Ideal.PowerQuotient.Hom.power_smul_le_ker (AdicCompletion.principalIdeal (DividedPowerEnvelope.Coordinates.completedRing E p) p)
      (coefficientModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F)
      ((moduleSpecΓFunctor (R := .of (stageRing p γ π hπ hJ hIC hpnil E hE e))).obj (F.obj ((stages p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ).obj e)))
      (limit.π (coefficientSystem p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F) (op e)))

variable [hcrystal : IsCrystal F] [hqc : IsLocallyQuasiCoherent F]

/-- The inverse-limit coefficient module of a quasi-coherent crystal is complete. -/
theorem coefficientModule_isAdicComplete :
    IsAdicComplete (AdicCompletion.principalIdeal (DividedPowerEnvelope.Coordinates.completedRing E p) p) (coefficientModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F) := sorry

/-- Reducing inverse-limit coefficients gives exactly the coefficients on a quotient thickening. -/
theorem coefficientQuotient_bijective (e : ℕ) :
    Function.Bijective (coefficientQuotient p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F e) := sorry

/-- The finite-stage tensor comparison is bijective for a quasi-coherent crystal. -/
theorem stageTensorComparison_bijective (e : ℕ) :
    Function.Bijective (stageTensorComparison p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F e) := sorry

/-- The completed algebraic tensor is canonically the limit of its geometric stage tensors. -/
theorem completedTensorComparison_bijective :
    Function.Bijective (completedTensorComparison p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F) := sorry

/-- The canonical crystalline connection evaluated on the actual coefficient projection. -/
private def stageConnectionValue (e : ℕ) :
    coefficientModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F →+ stageTensorModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F e :=
  ((canonicalConnectionHom F ((stages p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ).obj e)).val.app (op ⊤)).hom.toAddMonoidHom.comp
    (limit.π (coefficientSystem p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F) (op e)).hom.toAddMonoidHom

/-- The canonical crystalline connection values commute with the actual geometric transitions. -/
theorem stageConnection_naturality {i j : ℕᵒᵖ} (f : i ⟶ j) :
    AddCommGrpCat.ofHom (stageConnectionValue p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F i.unop) ≫ (stageTensorSystem p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F).map f =
      AddCommGrpCat.ofHom (stageConnectionValue p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F j.unop) := sorry

/-- The compatible finite-stage canonical connections induce an additive map to the tensor limit. -/
private def connectionToLimit : coefficientModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F →+ (limit (stageTensorSystem p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F) : AddCommGrpCat) :=
  (limit.lift (stageTensorSystem p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F)
    { pt := AddCommGrpCat.of (coefficientModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F)
      π :=
        { app := fun i ↦ AddCommGrpCat.ofHom (stageConnectionValue p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F i.unop)
          naturality := fun i j f ↦ (Category.id_comp _).trans
            (stageConnection_naturality p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F f).symm } }).hom

/-- Transport the compatible canonical connections through the constructed tensor comparison. -/
private def connectionAddMap : coefficientModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F →+ completedTensor p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F :=
  (AddEquiv.ofBijective (completedTensorComparison p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F)
    (completedTensorComparison_bijective p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F)).symm.toAddMonoidHom.comp
      (connectionToLimit p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F)

/-- The induced connection obeys the completed Leibniz identity for every completed scalar. -/
theorem connection_leibniz (r : (DividedPowerEnvelope.Coordinates.completedRing E p)) (m : coefficientModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F) :
    -- Local instance justification (noncanonical choice): the relative connection uses the coefficient action selected by the explicit polynomial envelope.
    letI := DividedPowerEnvelope.Coordinates.baseAlgebra E
    connectionAddMap p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F (r • m) = r • connectionAddMap p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F m +
      (AdicCompletion.of (AdicCompletion.principalIdeal (DividedPowerEnvelope.Coordinates.completedRing E p) p) _
        (m ⊗ₜ[(DividedPowerEnvelope.Coordinates.completedRing E p)] DPPolynomial.DeRham.completedDerivation A E.D E.D.dividedPowers p r) : completedTensor p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F) := sorry

/-- The completed connection induced by canonical crystalline connections on the quotient stages. -/
def connection :
    -- Local instance justification (noncanonical choice): the relative connection uses the coefficient action selected by the explicit polynomial envelope.
    letI := DividedPowerEnvelope.Coordinates.baseAlgebra E
    Connection.Adic A E.D E.D.dividedPowers p (coefficientModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F) :=
  -- Local instance justification (noncanonical choice): the relative connection uses the coefficient action selected by the explicit polynomial envelope.
  letI := DividedPowerEnvelope.Coordinates.baseAlgebra E
  Connection.Adic.of A E.D E.D.dividedPowers p (connectionAddMap p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F)
    (connection_leibniz p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F)

/-- The reconstructed connection is integrable. -/
theorem connection_isIntegrable :
    -- Local instance justification (noncanonical choice): the relative connection uses the coefficient action selected by the explicit polynomial envelope.
    letI := DividedPowerEnvelope.Coordinates.baseAlgebra E
    Connection.Adic.IsIntegrable A E.D E.D.dividedPowers p (connection p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F) := sorry

/-- The reconstructed connection is topologically quasi-nilpotent in every polynomial coordinate. -/
theorem connection_isTopologicallyQuasiNilpotent :
    -- Local instance justification (noncanonical choice): the relative connection uses the coefficient action selected by the explicit polynomial envelope.
    letI := DividedPowerEnvelope.Coordinates.baseAlgebra E
    Connection.Adic.IsTopologicallyQuasiNilpotent (connection p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F)
      (coefficientModule_isAdicComplete p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F) (DividedPowerEnvelope.Coordinates.completedCoord E hE p) := sorry

/-- The complete integrable quasi-nilpotent connection pair associated to a quasi-coherent crystal. -/
def connectionPair :
    -- Local instance justification (noncanonical choice): the relative connection uses the coefficient action selected by the explicit polynomial envelope.
    letI := DividedPowerEnvelope.Coordinates.baseAlgebra E
    Connection.Adic.quasiNilpotentCategory (A := A) (δ := E.D.dividedPowers)
      (DividedPowerEnvelope.Coordinates.completedCoord E hE p) :=
  -- Local instance justification (noncanonical choice): the relative connection uses the coefficient action selected by the explicit polynomial envelope.
  letI := DividedPowerEnvelope.Coordinates.baseAlgebra E
  ⟨coefficientModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F, connection p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F, coefficientModule_isAdicComplete p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F,
    connection_isIntegrable p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F, connection_isTopologicallyQuasiNilpotent p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F⟩

/-- The connection projection is precisely the canonical connection at the actual quotient stage. -/
theorem connection_π (e : ℕ) (m : coefficientModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F) :
    -- Local instance justification (noncanonical choice): the projected connection uses the coefficient algebra selected by the explicit envelope.
    letI := DividedPowerEnvelope.Coordinates.baseAlgebra E
    (limit.π (stageTensorSystem p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F) (op e)).hom
        (completedTensorComparison p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F ((connection p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F).toAddMonoidHom m)) =
      (canonicalConnection F ((stages p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ).obj e)).apply (op ⊤) ((limit.π (coefficientSystem p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F) (op e)).hom m) := sorry

/-- The reconstructed pair has complete coefficients, obeys Leibniz, has zero curvature,
and has coordinatewise nilpotent iterates modulo `p`. -/
theorem connectionPair_spec :
    -- Local instance justification (noncanonical choice): the relative connection uses the coefficient action selected by the explicit polynomial envelope.
    letI := DividedPowerEnvelope.Coordinates.baseAlgebra E
    ∃ hcomplete : IsAdicComplete (AdicCompletion.principalIdeal (DividedPowerEnvelope.Coordinates.completedRing E p) p) (coefficientModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F),
      (∀ (r : (DividedPowerEnvelope.Coordinates.completedRing E p)) (m : coefficientModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F),
        (connection p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F).toAddMonoidHom (r • m) = r • (connection p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F).toAddMonoidHom m +
          AdicCompletion.of (AdicCompletion.principalIdeal (DividedPowerEnvelope.Coordinates.completedRing E p) p) _
            (m ⊗ₜ[(DividedPowerEnvelope.Coordinates.completedRing E p)] DPPolynomial.DeRham.completedDerivation A E.D E.D.dividedPowers p r)) ∧
      Connection.Adic.IsIntegrable A E.D E.D.dividedPowers p (connection p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F) ∧
      Connection.Adic.IsTopologicallyQuasiNilpotent (connection p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F) hcomplete
        (DividedPowerEnvelope.Coordinates.completedCoord E hE p) := sorry


variable {G : CrisModuleSheaf (Spec (.of A)) IS γS hc X x₀}

/-- A crystalline module morphism induces the actual componentwise map of coefficient systems. -/
private def coefficientSystemMap (φ : F ⟶ G) : coefficientSystem p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F ⟶ coefficientSystem p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ G where
  app e := (ModuleCat.restrictScalars
    ((Scheme.ΓSpecIso (.of (stageRing p γ π hπ hJ hIC hpnil E hE e.unop))).inv.hom.comp
      (stageRingMap p γ π hπ hJ hIC hpnil E hE e.unop))).map
        ((φ.app ((stages p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ).obj e.unop)).val.app (op ⊤))
  naturality i j f :=
    ModuleCat.hom_ext (LinearMap.toAddMonoidHom_injective
      (congrArg AddCommGrpCat.Hom.hom
        (congrArg (fun h ↦ Scheme.Modules.Hom.app h ⊤)
          ((Scheme.Modules.pullbackPushforwardAdjunction
            ((stages p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ).map f.unop).hom.thickening).homEquiv_naturality_left_square
              (φ.app ((stages p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ).obj i.unop)) (G.comparison ((stages p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ).map f.unop))
              (F.comparison ((stages p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ).map f.unop)) (φ.app ((stages p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ).obj j.unop))
              (φ.natural ((stages p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ).map f.unop))))).symm)

/-- The inverse-limit coefficient map acts through the given crystalline module morphism. -/
def coefficientMap (φ : F ⟶ G) : coefficientModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F →ₗ[(DividedPowerEnvelope.Coordinates.completedRing E p)] coefficientModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ G :=
  (lim.map (coefficientSystemMap p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F φ)).hom

/-- The induced coefficient map respects the completed-envelope scalar action. -/
theorem coefficientMap_smul (φ : F ⟶ G) (r : (DividedPowerEnvelope.Coordinates.completedRing E p)) (m : coefficientModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F) :
    coefficientMap p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F φ (r • m) = r • coefficientMap p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F φ m := sorry

variable [IsCrystal G] [IsLocallyQuasiCoherent G]

/-- The actual coefficient map of a crystal morphism is horizontal for the reconstructed connections. -/
theorem connection_map_commutes (φ : F ⟶ G) (m : coefficientModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F) :
    -- Local instance justification (noncanonical choice): the relative connection uses the coefficient action selected by the explicit polynomial envelope.
    letI := DividedPowerEnvelope.Coordinates.baseAlgebra E
    (connection p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ G).toAddMonoidHom (coefficientMap p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F φ m) =
      Connection.Adic.tensorMap (δ := E.D.dividedPowers) (coefficientMap p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F φ)
        ((connection p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F).toAddMonoidHom m) := sorry

/-- The horizontal map associated to a morphism of quasi-coherent crystals. -/
def connectionMap (φ : F ⟶ G) :
    -- Local instance justification (noncanonical choice): the relative connection uses the coefficient action selected by the explicit polynomial envelope.
    letI := DividedPowerEnvelope.Coordinates.baseAlgebra E
    Connection.Adic.Hom (connection p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F) (connection p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ G) :=
  -- Local instance justification (noncanonical choice): the relative connection uses the coefficient action selected by the explicit polynomial envelope.
  letI := DividedPowerEnvelope.Coordinates.baseAlgebra E
  Connection.Adic.Hom.of (coefficientMap p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F φ) (connection_map_commutes p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F φ)

/-- The full category of crystals with locally quasi-coherent underlying modules. -/
abbrev quasiCoherentCrystals :=
  ObjectProperty.FullSubcategory (fun F : CrisModuleSheaf (Spec (.of A)) IS γS hc X x₀ ↦
    IsCrystal F ∧ IsLocallyQuasiCoherent F)

/-- The assignment on reconstructed connection pairs preserves the identity morphism. -/
theorem toConnectionPairs_map_id :
    -- Local instance justification (noncanonical choice): the relative connection uses the coefficient action selected by the explicit polynomial envelope.
    letI := DividedPowerEnvelope.Coordinates.baseAlgebra E
    connectionMap p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F (𝟙 F) = Connection.Adic.Hom.id (connection p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F) := sorry

/-- The assignment on reconstructed connection pairs preserves composition. -/
theorem toConnectionPairs_map_comp {H : CrisModuleSheaf (Spec (.of A)) IS γS hc X x₀}
    [IsCrystal H] [IsLocallyQuasiCoherent H] (φ : F ⟶ G) (ψ : G ⟶ H) :
    -- Local instance justification (noncanonical choice): the relative connection uses the coefficient action selected by the explicit polynomial envelope.
    letI := DividedPowerEnvelope.Coordinates.baseAlgebra E
    connectionMap p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F (φ ≫ ψ) =
      Connection.Adic.Hom.comp (connectionMap p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F φ) (connectionMap p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ G ψ) := sorry

/-- Quasi-coherent crystals determine complete integrable topologically quasi-nilpotent connections
by their canonical connections on the actual polynomial-envelope quotient thickenings. -/
def toConnectionPairs :
    -- Local instance justification (noncanonical choice): the relative connection uses the coefficient action selected by the explicit polynomial envelope.
    letI := DividedPowerEnvelope.Coordinates.baseAlgebra E
    quasiCoherentCrystals IS γS hc x₀ ⥤
    Connection.Adic.quasiNilpotentCategory (A := A) (δ := E.D.dividedPowers)
      (DividedPowerEnvelope.Coordinates.completedCoord E hE p) :=
  -- Local instance justification (noncanonical choice): the relative connection uses the coefficient action selected by the explicit polynomial envelope.
  letI := DividedPowerEnvelope.Coordinates.baseAlgebra E
  { obj F :=
      -- Local instance justification (proof-local temporary data): the full-subcategory object supplies its crystal law for evaluating the canonical crystalline connection.
      letI : IsCrystal F.obj := F.property.1
      -- Local instance justification (proof-local temporary data): the full-subcategory object supplies quasi-coherence for the affine completed tensor comparison.
      letI : IsLocallyQuasiCoherent F.obj := F.property.2
      connectionPair p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F.obj
    map {F G} φ :=
      -- Local instance justification (proof-local temporary data): source crystal law from its predicate.
      letI : IsCrystal F.obj := F.property.1
      -- Local instance justification (proof-local temporary data): source quasi-coherence from its predicate.
      letI : IsLocallyQuasiCoherent F.obj := F.property.2
      -- Local instance justification (proof-local temporary data): target crystal law from its predicate.
      letI : IsCrystal G.obj := G.property.1
      -- Local instance justification (proof-local temporary data): target quasi-coherence from its predicate.
      letI : IsLocallyQuasiCoherent G.obj := G.property.2
      connectionMap p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F.obj φ.hom
    map_id F :=
      -- Local instance justification (proof-local temporary data): source crystal law from its predicate.
      letI : IsCrystal F.obj := F.property.1
      -- Local instance justification (proof-local temporary data): source quasi-coherence from its predicate.
      letI : IsLocallyQuasiCoherent F.obj := F.property.2
      toConnectionPairs_map_id p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F.obj
    map_comp {F G H} φ ψ :=
      -- Local instance justification (proof-local temporary data): source crystal law from its predicate.
      letI : IsCrystal F.obj := F.property.1
      -- Local instance justification (proof-local temporary data): source quasi-coherence from its predicate.
      letI : IsLocallyQuasiCoherent F.obj := F.property.2
      -- Local instance justification (proof-local temporary data): intermediate crystal law from its predicate.
      letI : IsCrystal G.obj := G.property.1
      -- Local instance justification (proof-local temporary data): intermediate quasi-coherence from its predicate.
      letI : IsLocallyQuasiCoherent G.obj := G.property.2
      -- Local instance justification (proof-local temporary data): target crystal law from its predicate.
      letI : IsCrystal H.obj := H.property.1
      -- Local instance justification (proof-local temporary data): target quasi-coherence from its predicate.
      letI : IsLocallyQuasiCoherent H.obj := H.property.2
      toConnectionPairs_map_comp p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F.obj φ.hom ψ.hom }


/-- The coefficient projection of the functor's object is the actual inverse-limit projection. -/
theorem toConnectionPairs_obj_π (e : ℕ)
    (m : ((toConnectionPairs p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ).obj
      ⟨F, hcrystal, hqc⟩).1) :
    (limit.π (coefficientSystem p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F) (op e)).hom m =
      (limit.π (CechCrisCover.completedModuleSystem γ hIC hpnil IS γS hc x₀ eX.hom heX hI hγ
        inferInstance (envelopeObject p γ π hπ hJ hIC hpnil E hE) F) (op e)).hom m := sorry

/-- The coefficient map projects to the component of the given crystal morphism on stage sections. -/
theorem toConnectionPairs_map_π (φ : F ⟶ G) (e : ℕ) (m : coefficientModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F) :
    (limit.π (coefficientSystem p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ G) (op e)).hom (coefficientMap p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F φ m) =
      ((φ.app ((stages p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ).obj e)).val.app (op ⊤)).hom ((limit.π (coefficientSystem p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F) (op e)).hom m) := sorry

end CrystallineModuleSheaf.CrisModuleSheaf.Completed
