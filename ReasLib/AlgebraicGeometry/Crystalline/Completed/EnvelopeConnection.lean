/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Completed.StageConnection
public import ReasLib.RingTheory.DividedPowers.Envelope.Crystalline
public import ReasLib.RingTheory.Kaehler.DeRham.DividedPowers.AdicCompletion.Comparison
public import ReasLib.RingTheory.Kaehler.DeRham.Connection.Adic.QuasiNilpotent

@[expose] public section

noncomputable section

set_option backward.privateInPublic true
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Crystalline
open KaehlerDifferential.DeRham DividedPowers.PAdic DPPolynomial.DeRham
open scoped TensorProduct

universe u

namespace CrystallineModuleSheaf.CrisModuleSheaf.Completed.Envelope

variable (p : ℕ) [Fact p.Prime]
variable {A C P : Type u} [CommRing A] [CommRing C] [CommRing P]
variable [Algebra A C] [Algebra A P]
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable {I : Ideal A} (γ : DividedPowers I)
variable (π : P →ₐ[A] C) (hπ : Function.Surjective π)
variable {J : Ideal P} (hJ : J = RingHom.ker π.toRingHom)
variable (hIC : Ideal.map (algebraMap A C) I = ⊥) (hpnil : IsNilpotent (p : C))
variable {hIJ : Ideal.map (algebraMap A P) I ≤ J}
variable (E : DividedPowerEnvelope I γ (algebraMap A P) J hIJ)
variable (hE : DividedPowerEnvelope.IsUniversal γ (algebraMap A P) hIJ E)

/-- A nilpotence bound for the distinguished ideal of the universal envelope. -/
private def bound : ℕ :=
  (pAdicCompletionIsCrisWedgeObject p A P I γ C (algebraMap A C)
    π.toRingHom π.comp_algebraMap hIC J hJ hπ hpnil E hE).choose

/-- The bound puts the corresponding power of the principal ideal in the envelope ideal. -/
private theorem bound_le :
    Ideal.span {(p : E.D)} ^ bound p γ π hπ hJ hIC hpnil E hE ≤ E.D.ideal :=
  (pAdicCompletionIsCrisWedgeObject p A P I γ C (algebraMap A C)
    π.toRingHom π.comp_algebraMap hIC J hJ hπ hpnil E hE).choose_spec.2.choose

/-- The prime is nilpotent in the distinguished quotient of the envelope. -/
def quotientNilpotent : IsNilpotent (p : E.D ⧸ E.D.ideal) :=
  ⟨bound p γ π hπ hJ hIC hpnil E hE,
    (map_pow (Ideal.Quotient.mk E.D.ideal) (p : E.D) _).symm.trans
      ((Ideal.Quotient.eq_zero_iff_mem).mpr
        (bound_le p γ π hπ hJ hIC hpnil E hE
          (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_singleton (p : E.D))) _)))⟩

/-- The completed universal envelope with its extended divided powers and quotient to the fibre. -/
@[implicit_reducible] def envelopeObject :=
  let N := bound p γ π hπ hJ hIC hpnil E hE
  let hN := bound_le p γ π hπ hJ hIC hpnil E hE
  envelopeCompletedCrisObject p γ (algebraMap A C) π.toRingHom hπ π.comp_algebraMap
    hIC hpnil hJ E hE N hN (envelopeCompletionDividedPowers E N hN)
    (envelopeCompletionDividedPowers_isDPMorphism E N hN)

/-- The completed crystalline base map is the completion of the presentation's structural map. -/
theorem baseMap_eq :
    (envelopeObject p γ π hπ hJ hIC hpnil E hE).base.toRingHom =
      (algebraMap E.D (AdicCompletion (Ideal.span {(p : E.D)}) E.D)).comp
        (E.toD.comp (algebraMap A P)) :=
  congrArg (fun f : A →+* E.D ↦
    (algebraMap E.D (AdicCompletion (Ideal.span {(p : E.D)}) E.D)).comp f) E.base_toD

variable {γ}

/-- The completed coefficient ring of the universal envelope. -/
abbrev ring := AdicCompletion (Ideal.span {(p : E.D)}) E.D

variable (γ)

/-- The compatible extension transported to the image of the original divided-power ideal. -/
private def imageExtension :
    {δhat : DividedPowers (Ideal.map (algebraMap E.D (ring p E)) E.D.ideal) //
      E.D.dividedPowers.IsDPMorphism δhat (algebraMap E.D (ring p E))} :=
  let h := AdicCompletion.map_eq_ker_toQuotient (Ideal.span {(p : E.D)}) E.D.ideal
    (Submodule.fg_span_singleton (p : E.D))
    (bound p γ π hπ hJ hIC hpnil E hE) (bound_le p γ π hπ hJ hIC hpnil E hE)
  h.symm ▸ ⟨(envelopeObject p γ π hπ hJ hIC hpnil E hE).B.dividedPowers,
    envelopeCompletionDividedPowers_isDPMorphism E _ _⟩

/-- The canonical extended divided powers on the image ideal in the completed envelope. -/
def completionPowers := (imageExtension p γ π hπ hJ hIC hpnil E hE).val

/-- The canonical image-ideal divided powers extend the original envelope divided powers. -/
theorem completionPowers_extends :
    E.D.dividedPowers.IsDPMorphism (completionPowers p γ π hπ hJ hIC hpnil E hE)
      (algebraMap E.D (ring p E)) :=
  (imageExtension p γ π hπ hJ hIC hpnil E hE).property

variable {γ}

/-- Connections relative to the base map of the specified envelope. -/
abbrev connectionType (M : ModuleCat.{u} (ring p E)) :=
  -- Local instance justification (noncanonical choice): the explicit envelope selects the structural map defining relative differentials.
  letI := (E.toD.comp (algebraMap A P)).toAlgebra
  Connection.Adic A E.D E.D.dividedPowers p M

variable (γ)

/-- Completed forms on the original envelope identify with those on its completion. -/
private def originalFormsEquiv :=
  DividedPowerDifferential.completedFormsEquivOfExtension
    (E.toD.comp (algebraMap A P)) E.D.dividedPowers p
    (quotientNilpotent p γ π hπ hJ hIC hpnil E hE)
    (bound p γ π hπ hJ hIC hpnil E hE) (bound_le p γ π hπ hJ hIC hpnil E hE)
    (envelopeObject p γ π hπ hJ hIC hpnil E hE).B.dividedPowers
    (envelopeCompletionDividedPowers_isDPMorphism E _ _)

/-- The completed differential module on the actual completed crystalline envelope. -/
def completedForms : ModuleCat.{u} (ring p E) :=
  ModuleCat.of (envelopeObject p γ π hπ hJ hIC hpnil E hE).B
    (CrystallineStagePDConnection.completedOneForms γ hIC hpnil (envelopeObject p γ π hπ hJ hIC hpnil E hE))

/-- Completed original-envelope forms identify with the actual completed crystalline envelope forms. -/
def formsEquiv :
    DividedPowerDifferential.originalCompletion
      (E.toD.comp (algebraMap A P)) E.D.dividedPowers p ≃ₗ[ring p E] completedForms p γ π hπ hJ hIC hpnil E hE :=
  let h := congrArg (fun f : A →+* E.D ↦ (algebraMap E.D (ring p E)).comp f) E.base_toD
  let forms (f : A →+* ring p E) : ModuleCat.{u} (ring p E) :=
    ModuleCat.of (ring p E) (AdicCompletion (Ideal.span {(p : ring p E)})
      (dividedPowerDifferential f (envelopeObject p γ π hπ hJ hIC hpnil E hE).B.dividedPowers))
  (originalFormsEquiv p γ π hπ hJ hIC hpnil E hE).trans (eqToIso (congrArg forms h.symm)).toLinearEquiv

variable {X : Scheme.{u}} (IS : (Spec (.of A)).IdealSheafData)
variable (γS : ∀ V : (Spec (.of A)).affineOpens, DividedPowers (IS.ideal V))
variable (hc : ∀ (V : (Spec (.of A)).affineOpens) (a : Γ(Spec (.of A), V)),
  (γS V).IsDPMorphism (γS ((Spec (.of A)).affineBasicOpen a))
    ((Spec (.of A)).presheaf.map (homOfLE ((Spec (.of A)).basicOpen_le a)).op).hom)
variable (x₀ : X ⟶ IS.subscheme) (eX : Spec (.of C) ≅ X)
variable (heX : eX.hom ≫ x₀ ≫ IS.subschemeι = Spec.map (CommRingCat.ofHom (algebraMap A C)))
variable (hI : IS = DividedPowers.affineIdeal (I := I))
variable (hγ : DividedPowers.IsDPMorphism γ
  (γS ⟨⊤, isAffineOpen_top (Spec (.of A))⟩) (Scheme.ΓSpecIso (.of A)).inv.hom)
variable (F : CrisModuleSheaf (Spec (.of A)) IS γS hc X x₀)

/-- The genuine geometric quotient stages of a completed universal envelope. -/
abbrev stages :=
  CechCrisCover.completedSmallSystem γ hIC hpnil IS γS hc x₀ eX.hom heX hI hγ inferInstance (envelopeObject p γ π hπ hJ hIC hpnil E hE)

/-- The inverse system of actual crystalline coefficients, with envelope scalars. -/
abbrev coefficientSystem :=
  CrystallineStagePDConnection.envelopeSystem γ hIC hpnil IS γS hc x₀ eX.hom heX hI hγ inferInstance (envelopeObject p γ π hπ hJ hIC hpnil E hE) F

/-- The inverse limit of the actual crystalline coefficient modules. -/
def coefficientModule : ModuleCat.{u} (ring p E) :=
  CrystallineStagePDConnection.completedModule γ hIC hpnil IS γS hc x₀ eX.hom heX hI hγ inferInstance (envelopeObject p γ π hπ hJ hIC hpnil E hE) F

/-- The coefficient projection to the actual shifted quotient stage. -/
abbrev coefficientProjection (e : ℕ) :=
  CrystallineStagePDConnection.coefficientProjection γ hIC hpnil IS γS hc x₀ eX.hom heX hI hγ inferInstance (envelopeObject p γ π hπ hJ hIC hpnil E hE) F e

variable [IsCrystal F] [IsLocallyQuasiCoherent F]

/-- The inverse limit of crystalline coefficients is complete for the principal-adic topology. -/
theorem coefficientModule_isAdicComplete :
    IsAdicComplete (Ideal.span {(p : ring p E)}) (coefficientModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F) := sorry

/-- Complete coefficients identify with completed degree-zero tensors through the canonical tensor unit. -/
private def degreeZeroEquiv :
    coefficientModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F ≃+
      CrystallineStagePDConnection.completedTensorTerm γ hIC hpnil IS γS hc x₀ eX.hom heX hI hγ inferInstance (envelopeObject p γ π hπ hJ hIC hpnil E hE) F 0 :=
  -- Local instance justification (proof-local temporary data): completeness of this actual crystalline coefficient limit is the named completion law.
  letI := coefficientModule_isAdicComplete p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F
  -- Local instance justification (instance diamond): completion of the tensor unit uses the tensor action fixed by the stage complex.
  letI : Module (ring p E)
      (coefficientModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F ⊗[ring p E] ring p E) := TensorProduct.instModule
  (AdicCompletion.ofLinearEquiv (Ideal.span {(p : ring p E)})
    (coefficientModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F)).toAddEquiv.trans
      (AdicCompletion.congr (Ideal.span {(p : ring p E)})
        (TensorProduct.rid (ring p E) (coefficientModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F)).symm).toAddEquiv

/-- The canonical degree-zero map uses completeness and the tensor right unit. -/
private def degreeZero := (degreeZeroEquiv p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F).toAddMonoidHom

/-- Completed degree-one tensors are compared using the canonical differential completion equivalence. -/
private def degreeOne :
    CrystallineStagePDConnection.completedTensorTerm γ hIC hpnil IS γS hc x₀ eX.hom heX hI hγ inferInstance (envelopeObject p γ π hπ hJ hIC hpnil E hE) F 1 →+
      completedTensorB (ring p E) p (coefficientModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F)
        (DividedPowerDifferential.originalCompletion
          (E.toD.comp (algebraMap A P)) E.D.dividedPowers p) :=
  (AdicCompletion.map (M := coefficientModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F ⊗[ring p E] completedForms p γ π hπ hJ hIC hpnil E hE) (Ideal.span {(p : ring p E)})
    (TensorProduct.map (LinearMap.id : coefficientModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F →ₗ[ring p E] _)
      (formsEquiv p γ π hπ hJ hIC hpnil E hE).symm.toLinearMap)).toAddMonoidHom

/-- The completed additive connection is transported from the actual inverse-limit differential. -/
private def connectionAddMap :=
  (degreeOne p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F).comp
    ((CrystallineStagePDConnection.completedDifferential γ hIC hpnil IS γS hc x₀ eX.hom heX hI hγ inferInstance (envelopeObject p γ π hπ hJ hIC hpnil E hE) F 0).comp
      (degreeZero p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F))

/-- The canonical completed differential satisfies the scalar Leibniz identity. -/
theorem connection_leibniz (r : ring p E) (m : coefficientModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F) :
    connectionAddMap p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F (r • m) =
      r • connectionAddMap p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F m +
        AdicCompletion.of (Ideal.span {(p : ring p E)}) _
          (m ⊗ₜ[ring p E] AdicCompletion.completeAddMap E.D E.D p
            (dividedPowerDifferentialDerivation
              (E.toD.comp (algebraMap A P)) E.D.dividedPowers).toAddMonoidHom r) := sorry

/-- The connection on crystalline coefficients is induced by the actual quotient-stage differentials. -/
def connection : connectionType p E (coefficientModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F) :=
  -- Local instance justification (noncanonical choice): the connection structure is relative to the explicit envelope's structural map.
  letI := (E.toD.comp (algebraMap A P)).toAlgebra
  { toAddMonoidHom := connectionAddMap p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F
    leibniz := connection_leibniz p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F }

/-- The canonical crystalline connection has zero intrinsic curvature. -/
theorem connection_isIntegrable :
    -- Local instance justification (noncanonical choice): intrinsic curvature is relative to this envelope's structural map.
    letI := (E.toD.comp (algebraMap A P)).toAlgebra
    Connection.Adic.IsIntegrable A E.D E.D.dividedPowers p (connection p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F) := sorry

/-- Projection of a completed original-envelope coefficient tensor to the actual crystalline one-form stage. -/
def tensorProjection (e : ℕ) :
    completedTensorB (ring p E) p (coefficientModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F)
      (DividedPowerDifferential.originalCompletion
        (E.toD.comp (algebraMap A P)) E.D.dividedPowers p) →+
      (CrystallineStagePDConnection.deRhamComplex γ hIC hpnil IS γS hc x₀ eX.hom heX hI hγ inferInstance (envelopeObject p γ π hπ hJ hIC hpnil E hE) F e).X 1 :=
  (CrystallineStagePDConnection.completedTensorProjection γ hIC hpnil IS γS hc x₀ eX.hom heX hI hγ inferInstance (envelopeObject p γ π hπ hJ hIC hpnil E hE) F e 1).comp
    (AdicCompletion.map (M := coefficientModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F ⊗[ring p E] DividedPowerDifferential.originalCompletion (E.toD.comp (algebraMap A P)) E.D.dividedPowers p) (Ideal.span {(p : ring p E)})
      (TensorProduct.map
        (LinearMap.id : coefficientModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F →ₗ[ring p E] _)
        (formsEquiv p γ π hπ hJ hIC hpnil E hE).toLinearMap)).toAddMonoidHom

/-- At each actual quotient stage the completed connection recovers the crystalline differential. -/
theorem connection_π (e : ℕ) (m : coefficientModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F) :
    -- Local instance justification (noncanonical choice): connection operations are relative to this explicit envelope's structural map.
    letI := (E.toD.comp (algebraMap A P)).toAlgebra
    tensorProjection p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F e ((connection p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F).toAddMonoidHom m) =
      (CrystallineStagePDConnection.deRhamComplex γ hIC hpnil IS γS hc x₀ eX.hom heX hI hγ inferInstance (envelopeObject p γ π hπ hJ hIC hpnil E hE) F e).d 0 1
        (coefficientProjection p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F e m) := sorry

variable {G : CrisModuleSheaf (Spec (.of A)) IS γS hc X x₀}

/-- A crystalline coefficient morphism acts on each actual stage through its section map. -/
private def coefficientStageMap (φ : F ⟶ G) (e : ℕ) :
    (coefficientSystem p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F).obj (op e) ⟶ (coefficientSystem p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ G).obj (op e) :=
  (ModuleCat.restrictScalars
    ((Scheme.ΓSpecIso (.of (CrystallineStagePDConnection.ring γ hIC hpnil
      (envelopeObject p γ π hπ hJ hIC hpnil E hE) e))).inv.hom.comp
        (pAdicQuotientMk γ (algebraMap A C) hIC hpnil
          (envelopeObject p γ π hπ hJ hIC hpnil E hE) e).toRingHom)).map
    ((φ.app ((stages p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ).obj e)).val.app (op ⊤))

/-- Stagewise section maps commute with the genuine crystalline coefficient restrictions. -/
theorem coefficientSystemMap_naturality (φ : F ⟶ G) {i j : ℕᵒᵖ} (a : i ⟶ j) :
    (coefficientSystem p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F).map a ≫ coefficientStageMap p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F φ j.unop =
      coefficientStageMap p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F φ i.unop ≫ (coefficientSystem p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ G).map a := sorry

/-- The natural transformation of coefficient systems uses the actual stage section maps. -/
private def coefficientSystemMap (φ : F ⟶ G) :
    coefficientSystem p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F ⟶ coefficientSystem p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ G where
  app e := coefficientStageMap p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F φ e.unop
  naturality := fun _ _ a ↦ coefficientSystemMap_naturality p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F φ a

/-- The inverse-limit coefficient map induced by a crystalline module morphism. -/
def coefficientMap (φ : F ⟶ G) :
    coefficientModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F →ₗ[ring p E] coefficientModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ G :=
  (lim.map (coefficientSystemMap p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F φ)).hom

/-- The inverse-limit coefficient map respects completed-envelope scalars. -/
theorem coefficientMap_smul (φ : F ⟶ G) (r : ring p E) (m : coefficientModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F) :
    coefficientMap p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F φ (r • m) = r • coefficientMap p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F φ m := sorry

variable [IsCrystal G] [IsLocallyQuasiCoherent G]

/-- The induced coefficient map is horizontal for the canonical completed connections. -/
theorem connection_map_commutes (φ : F ⟶ G) (m : coefficientModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F) :
    -- Local instance justification (noncanonical choice): connection operations are relative to this explicit envelope's structural map.
    letI := (E.toD.comp (algebraMap A P)).toAlgebra
    (connection p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ G).toAddMonoidHom (coefficientMap p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F φ m) =
      Connection.Adic.tensorMap (δ := E.D.dividedPowers) (coefficientMap p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F φ)
        ((connection p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F).toAddMonoidHom m) := sorry

/-- A crystalline module morphism induces its actual horizontal coefficient map. -/
def connectionMap (φ : F ⟶ G) :
    -- Local instance justification (noncanonical choice): connection operations are relative to this explicit envelope's structural map.
    letI := (E.toD.comp (algebraMap A P)).toAlgebra
    Connection.Adic.Hom (connection p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F) (connection p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ G) :=
  -- Local instance justification (noncanonical choice): connection operations are relative to this explicit envelope's structural map.
  letI := (E.toD.comp (algebraMap A P)).toAlgebra
  Connection.Adic.Hom.of (coefficientMap p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F φ)
    (connection_map_commutes p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F φ)

/-- The horizontal coefficient construction preserves identity morphisms. -/
theorem connectionMap_id :
    -- Local instance justification (noncanonical choice): connection operations are relative to this explicit envelope's structural map.
    letI := (E.toD.comp (algebraMap A P)).toAlgebra
    connectionMap p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F (𝟙 F) = Connection.Adic.Hom.id (connection p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F) := sorry

/-- The horizontal coefficient construction preserves composition. -/
theorem connectionMap_comp
    {H : CrisModuleSheaf (Spec (.of A)) IS γS hc X x₀}
    [IsCrystal H] [IsLocallyQuasiCoherent H] (φ : F ⟶ G) (ψ : G ⟶ H) :
    -- Local instance justification (noncanonical choice): connection operations are relative to this explicit envelope's structural map.
    letI := (E.toD.comp (algebraMap A P)).toAlgebra
    connectionMap p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F (φ ≫ ψ) =
      Connection.Adic.Hom.comp (connectionMap p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F φ) (connectionMap p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ G ψ) := sorry

/-- Each inverse-limit coefficient map projects to the given morphism on actual stage sections. -/
theorem coefficientMap_π (φ : F ⟶ G) (e : ℕ) (m : coefficientModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F) :
    coefficientProjection p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ G e (coefficientMap p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F φ m) =
      coefficientStageMap p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F φ e (coefficientProjection p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F e m) := sorry

end CrystallineModuleSheaf.CrisModuleSheaf.Completed.Envelope
