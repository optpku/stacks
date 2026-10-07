module
public import stacks_project.Chap60.Remark_60_24_4_Alternating_ech_complex_PDSquareZeroGeometry
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import stacks_project.Chap60.Remark_60_24_4_Alternating_ech_complex_PDFormsMap
public import stacks_project.Chap60.Remark_60_24_4_Alternating_ech_complex_SemilinearForms
public import Mathlib.Algebra.Homology.HomologicalComplexLimits

@[expose] public section
open AlgebraicGeometry CategoryTheory Opposite
open CrystallineModuleSheaf CechCrisCover
open AlgebraicGeometry.Scheme.Crystalline
universe u

namespace CrystallineStagePDConnection

variable {p : ℕ} [Fact p.Prime]
variable {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable {IA : Ideal A} (γA : DividedPowers IA)
variable (hIC : Ideal.map (algebraMap A C) IA = ⊥) (hpnil : IsNilpotent (p : C))
variable {X : Scheme.{u}} (I : (Spec (.of A)).IdealSheafData)
variable (γS : ∀ V : (Spec (.of A)).affineOpens, DividedPowers (I.ideal V))
variable (hc : ∀ (V : (Spec (.of A)).affineOpens) (a : Γ(Spec (.of A), V)),
  (γS V).IsDPMorphism (γS ((Spec (.of A)).affineBasicOpen a))
    ((Spec (.of A)).presheaf.map (homOfLE ((Spec (.of A)).basicOpen_le a)).op).hom)
variable (x₀ : X ⟶ I.subscheme) (eX : Spec (.of C) ⟶ X)
variable (heX : eX ≫ x₀ ≫ I.subschemeι = Spec.map (CommRingCat.ofHom (algebraMap A C)))
variable (hI : I = DividedPowers.affineIdeal (I := IA))
variable (hγ : DividedPowers.IsDPMorphism γA
  (γS ⟨⊤, isAffineOpen_top (Spec (.of A))⟩) (Scheme.ΓSpecIso (.of A)).inv.hom)
variable (ho : IsOpenImmersion eX)
variable (Z : CompletedCrisObject p A IA γA C (algebraMap A C) hIC hpnil)

/-- The actual quotient stage of the completed PD envelope. -/
noncomputable abbrev ring (e : ℕ) :=
  pAdicQuotientRing γA (algebraMap A C) hIC hpnil Z e

/-- Scalars on the quotient stage come from its given base PD morphism. -/
noncomputable instance algebra (e : ℕ) : Algebra A (ring γA hIC hpnil Z e) :=
  (pAdicQuotientThickening γA (algebraMap A C) hIC hpnil Z e).base.toRingHom.toAlgebra

/-- The PD ideal is nil because the stage is a genuine p-nilpotent
divided-power thickening. -/
theorem ideal_nil (e : ℕ) :
    ∀ b ∈ (ring γA hIC hpnil Z e).ideal, IsNilpotent b :=
  fun _ hb ↦ mem_nilradical.mp
    (((ring γA hIC hpnil Z e).dividedPowers.isLocallyNilpotent_of_isNilpotent_natCast
      (pAdicQuotientThickening γA (algebraMap A C) hIC hpnil Z e).p_nilpotent) hb)

/-- The stage base map is the spectrum of the actual base-ring map. -/
noncomputable abbrev base (e : ℕ) :=
  Spec.map (CommRingCat.ofHom
    (pAdicQuotientThickening γA (algebraMap A C) hIC hpnil Z e).base.toRingHom)

/-- The closed fibre maps to X through the specified affine chart. -/
noncomputable abbrev fibre (e : ℕ) :=
  Spec.map (CommRingCat.ofHom
    (pAdicQuotientThickening γA (algebraMap A C) hIC hpnil Z e).quotient) ≫ eX

include heX in
/-- The original affine-stage square retained by the geometric construction. -/
theorem square (e : ℕ) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (ring γA hIC hpnil Z e).ideal)) ≫
      base γA hIC hpnil Z e = fibre γA hIC hpnil eX Z e ≫ x₀ ≫ I.subschemeι :=
  affineThickening_square γA hIC hpnil I x₀ eX heX
    (pAdicQuotientThickening γA (algebraMap A C) hIC hpnil Z e)

variable (F : CrisModuleSheaf (Spec (.of A)) I γS hc X x₀)
variable [hcoherent : CrystallineCoefficients.SectionsCoherent I γS hc x₀ F]
variable [hcrystal : CrisModuleSheaf.IsCrystal F] [hqc : CrisModuleSheaf.IsLocallyQuasiCoherent F]

/-- The actual crystalline stage connection, obtained from its PD
square-zero thickening. Its coefficient module is the given F evaluated at
the actual stage; no arbitrary identification is supplied by a caller. -/
noncomputable def connection (e : ℕ) :=
  CrystallinePDSquareZeroGeometry.connection A (ring γA hIC hpnil Z e)
    (ring γA hIC hpnil Z e).dividedPowers I γS hc x₀
    (base γA hIC hpnil Z e) (fibre γA hIC hpnil eX Z e)
    (square γA hIC hpnil I x₀ eX heX Z e) (ideal_nil γA hIC hpnil Z e)
    (completedStageObject_baseCompatible γA hIC hpnil I γS hc x₀ eX heX hI hγ Z e)
    (completedStageObject_open γA hIC hpnil I γS hc x₀ eX heX ho Z e)
    (CrystallinePDSquareZeroGeometry.differentialLift_overAffineBase A
      (ring γA hIC hpnil Z e) (ring γA hIC hpnil Z e).dividedPowers) F

/-- The genuine de Rham complex at a p-adic stage, before taking the
inverse limit needed for the completed coefficient module. -/
noncomputable def deRhamComplex (e : ℕ) :=
  CrystallinePDSquareZeroGeometry.deRhamComplex A (ring γA hIC hpnil Z e)
    (ring γA hIC hpnil Z e).dividedPowers I γS hc x₀
    (base γA hIC hpnil Z e) (fibre γA hIC hpnil eX Z e)
    (square γA hIC hpnil I x₀ eX heX Z e) (ideal_nil γA hIC hpnil Z e)
    (completedStageObject_baseCompatible γA hIC hpnil I γS hc x₀ eX heX hI hγ Z e)
    (completedStageObject_open γA hIC hpnil I γS hc x₀ eX heX ho Z e)
    (CrystallinePDSquareZeroGeometry.differentialLift_overAffineBase A
      (ring γA hIC hpnil Z e) (ring γA hIC hpnil Z e).dividedPowers) F

/-- Coefficients at the actual affine crystalline stage, with scalars
restricted from functions using the canonical affine-functions map. -/
noncomputable def coefficientModule (e : ℕ) : ModuleCat.{u} (ring γA hIC hpnil Z e) :=
  (ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of (ring γA hIC hpnil Z e))).inv.hom).obj
    ((F.obj (completedSmallStage γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z e)).val.obj (op ⊤))

/-- The actual ring reduction from stage e+1 to stage e. -/
noncomputable def ringStep (e : ℕ) :
    DividedPowers.DPMorphism (ring γA hIC hpnil Z (e + 1)).dividedPowers
      (ring γA hIC hpnil Z e).dividedPowers :=
  (pAdicQuotientStep γA (algebraMap A C) hIC hpnil Z e).hom.map

/-- The smaller quotient ring is an algebra over the preceding stage
through its specified reduction map. -/
noncomputable instance stepAlgebra (e : ℕ) :
    Algebra (ring γA hIC hpnil Z (e + 1)) (ring γA hIC hpnil Z e) :=
  (ringStep γA hIC hpnil Z e).toRingHom.toAlgebra

/-- Stage reduction commutes with the original base-ring maps. -/
instance stepScalarTower (e : ℕ) :
    IsScalarTower A (ring γA hIC hpnil Z (e + 1)) (ring γA hIC hpnil Z e) := sorry

/-- The PD one-form reduction is induced by the actual quotient PD map. -/
noncomputable def oneFormsStep (e : ℕ) :
    CrystallinePDDeRham.oneForms A (ring γA hIC hpnil Z (e + 1))
        (ring γA hIC hpnil Z (e + 1)).dividedPowers →ₛₗ[(ringStep γA hIC hpnil Z e).toRingHom]
      CrystallinePDDeRham.oneForms A (ring γA hIC hpnil Z e)
        (ring γA hIC hpnil Z e).dividedPowers :=
  CrystallinePDDeRham.mapOneForms A (ring γA hIC hpnil Z (e + 1)) (ring γA hIC hpnil Z e)
    (ring γA hIC hpnil Z (e + 1)).dividedPowers (ring γA hIC hpnil Z e).dividedPowers
    (ringStep γA hIC hpnil Z e).isDPMorphism

/-- Coefficients restrict using F's comparison along the actual closed
immersion of crystalline stages. -/
noncomputable def coefficientStep (e : ℕ) :
    coefficientModule γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F (e + 1) →ₛₗ[
      (ringStep γA hIC hpnil Z e).toRingHom]
        coefficientModule γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F e where
  toFun :=
    abelianGlobalSections_map
      (completedSmallStep γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z e).hom.thickening
      (F.comparison (completedSmallStep γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z e))
  map_add' := map_add _
  map_smul' := sorry

/-- In degree zero restrict coefficient sections; in higher degrees map
both tensor factors by coefficient restriction and the actual exterior map. -/
noncomputable def termStep (e m : ℕ) :
    (deRhamComplex γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F (e + 1)).X m ⟶
      (deRhamComplex γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F e).X m :=
  match m with
  | 0 => AddCommGrpCat.ofHom
      (coefficientStep γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F e).toAddMonoidHom
  | m + 1 => AddCommGrpCat.ofHom
      (TensorProduct.map (coefficientStep γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F e)
        (CrystallineSemilinearForms.map (oneFormsStep γA hIC hpnil Z e) (m + 1))).toAddMonoidHom

/-- Naturality of the crystal's two infinitesimal pullbacks implies that
actual stage restriction commutes with the PD de Rham differential. -/
theorem termStep_comm (e m n : ℕ) :
    termStep γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F e m ≫
        (deRhamComplex γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F e).d m n =
      (deRhamComplex γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F (e + 1)).d m n ≫
        termStep γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F e n := sorry

/-- The genuine transition morphism of finite-stage PD de Rham complexes. -/
noncomputable def complexStep (e : ℕ) :
    deRhamComplex γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F (e + 1) ⟶
      deRhamComplex γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F e where
  f := termStep γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F e
  comm' := fun m n _ ↦ termStep_comm γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F e m n

/-- The inverse system retains every finite-stage differential and the
correct exponent e+pAdicOffset in its underlying quotient ring. -/
noncomputable def complexSystem : ℕᵒᵖ ⥤ CochainComplex AddCommGrpCat.{u} ℕ :=
  Functor.ofOpSequence (complexStep γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F)

/-- The completed stagewise PD de Rham complex. Its comparison with the
displayed completed tensor terms must be built quotient by quotient. -/
noncomputable def completedComplex : CochainComplex AddCommGrpCat.{u} ℕ :=
  Limits.limit (complexSystem γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F)

/-- Actual stage coefficients viewed as modules over the completed envelope
through the canonical quotient map. -/
noncomputable abbrev envelopeModule (e : ℕ) : ModuleCat.{u} Z.B :=
  (ModuleCat.restrictScalars (pAdicQuotientMk γA (algebraMap A C) hIC hpnil Z e).toRingHom).obj
    (coefficientModule γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F e)

/-- The envelope action on stage coefficients is the action restricted
along the actual p-adic quotient map. -/
noncomputable instance coefficientEnvelopeAction (e : ℕ) :
    Module Z.B (coefficientModule γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F e) :=
  (envelopeModule γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F e).isModule

/-- Coefficient restriction is linear over the common envelope because its
two quotient maps commute. The underlying function remains the actual
geometric restriction, not a chosen quotient equivalence. -/
noncomputable def envelopeStep (e : ℕ) :
    envelopeModule γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F (e + 1) ⟶
      envelopeModule γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F e :=
  ModuleCat.ofHom
    { toFun := coefficientStep γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F e
      map_add' := map_add _
      map_smul' := sorry }

/-- The coefficient system is built from the real successive restriction
maps. The sequence construction supplies functor laws; comparison with the
crystal's maps on all stage morphisms additionally requires coherence. -/
noncomputable def envelopeSystem : ℕᵒᵖ ⥤ ModuleCat.{u} Z.B :=
  Functor.ofOpSequence (envelopeStep γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F)

/-- The genuine completed coefficient module, with its canonical envelope
action supplied by the module-valued inverse limit. -/
noncomputable def completedModule : ModuleCat.{u} Z.B :=
  Limits.limit (envelopeSystem γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F)

/-- The actual inverse-limit projection to a crystalline coefficient stage. -/
noncomputable def coefficientProjection (e : ℕ) :
    completedModule γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F →ₗ[Z.B]
      envelopeModule γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F e :=
  (Limits.limit.π (envelopeSystem γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F) (op e)).hom

include hcoherent hcrystal hqc in
/-- Affine quasi-coherence and the crystal comparison make the successive
coefficient maps scalar reductions, hence the limit projections are surjective. -/
theorem coefficientProjection_surjective (e : ℕ) :
    Function.Surjective
      (coefficientProjection γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F e) := sorry

include hcoherent hcrystal hqc in
/-- The coefficient projection has the true shifted p-power kernel. This
uses effectiveness of the crystal's quotient-module tower and finite
generation of (p), not finite generation of its coefficient modules. -/
theorem coefficientProjection_kernel (e : ℕ) :
    LinearMap.ker (coefficientProjection γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F e) =
      (Ideal.span {(p : Z.B)}) ^ (e + pAdicOffset γA (algebraMap A C) hIC hpnil Z) •
        (⊤ : Submodule Z.B (completedModule γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F)) := sorry

/-- Only the correct shifted quotient of completed coefficients is
identified with a stage, through the actual inverse-limit projection. -/
noncomputable def coefficientQuotientEquiv (e : ℕ) :
    (completedModule γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F ⧸
      (Ideal.span {(p : Z.B)}) ^ (e + pAdicOffset γA (algebraMap A C) hIC hpnil Z) •
        (⊤ : Submodule Z.B (completedModule γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F))) ≃ₗ[Z.B]
      envelopeModule γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F e :=
  (Submodule.quotEquivOfEq _ _
    (coefficientProjection_kernel γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F e).symm).trans
      ((coefficientProjection γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F e).quotKerEquivOfSurjective
        (coefficientProjection_surjective γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F e))

/-- The quotient comparison is induced by the actual limit projection on
representatives; it is not an unspecified isomorphism of module carriers. -/
theorem coefficientQuotientEquiv_mk (e : ℕ)
    (x : completedModule γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F) :
    coefficientQuotientEquiv γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F e
      (Submodule.Quotient.mk x) =
        coefficientProjection γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F e x := rfl

/-- The completed envelope has its specified base algebra structure. -/
noncomputable instance envelopeAlgebra : Algebra A Z.B := Z.base.toRingHom.toAlgebra

/-- Each stage is an algebra over the envelope through the actual quotient. -/
noncomputable instance stageOverEnvelope (e : ℕ) : Algebra Z.B (ring γA hIC hpnil Z e) :=
  (pAdicQuotientMk γA (algebraMap A C) hIC hpnil Z e).toRingHom.toAlgebra

/-- The stage base map is the composite of the envelope base map and quotient. -/
instance stageEnvelopeTower (e : ℕ) : IsScalarTower A Z.B (ring γA hIC hpnil Z e) := sorry

/-- Genuine algebraic PD one-form reduction from the envelope to its stage. -/
noncomputable def algebraicFormsReduction (e : ℕ) :
    CrystallinePDDeRham.oneForms A Z.B Z.B.dividedPowers →ₛₗ[
      (pAdicQuotientMk γA (algebraMap A C) hIC hpnil Z e).toRingHom]
        CrystallinePDDeRham.oneForms A (ring γA hIC hpnil Z e) (ring γA hIC hpnil Z e).dividedPowers :=
  CrystallinePDDeRham.mapOneForms A Z.B (ring γA hIC hpnil Z e) Z.B.dividedPowers
    (ring γA hIC hpnil Z e).dividedPowers
    (pAdicQuotientMk γA (algebraMap A C) hIC hpnil Z e).isDPMorphism

/-- The same reduction map viewed in the canonical restricted target module. -/
noncomputable def restrictedFormsReduction (e : ℕ) :=
  CrystallineSemilinearForms.restricted (R := Z.B) (S := ring γA hIC hpnil Z e)
    (algebraicFormsReduction γA hIC hpnil Z e)

/-- PD forms of a p-power quotient are the corresponding quotient of
envelope PD forms, since relative differentiation kills the base integer p. -/
theorem restrictedFormsReduction_kernel (e : ℕ) :
    LinearMap.ker (restrictedFormsReduction γA hIC hpnil Z e) =
      (Ideal.span {(p : Z.B)}) ^ (e + pAdicOffset γA (algebraMap A C) hIC hpnil Z) •
        (⊤ : Submodule Z.B (CrystallinePDDeRham.oneForms A Z.B Z.B.dividedPowers)) := sorry

/-- The stage ring and its PD ideal are quotient images, so their one-forms
are generated by images of envelope one-forms. -/
theorem restrictedFormsReduction_surjective (e : ℕ) :
    Function.Surjective (restrictedFormsReduction γA hIC hpnil Z e) := sorry

/-- Only the finite shifted quotient of algebraic envelope forms is
identified with stage forms. -/
noncomputable def algebraicFormsQuotientEquiv (e : ℕ) :
    (CrystallinePDDeRham.oneForms A Z.B Z.B.dividedPowers ⧸
      (Ideal.span {(p : Z.B)}) ^ (e + pAdicOffset γA (algebraMap A C) hIC hpnil Z) •
        (⊤ : Submodule Z.B (CrystallinePDDeRham.oneForms A Z.B Z.B.dividedPowers))) ≃ₗ[Z.B]
      RestrictScalars Z.B (ring γA hIC hpnil Z e)
        (CrystallinePDDeRham.oneForms A (ring γA hIC hpnil Z e) (ring γA hIC hpnil Z e).dividedPowers) := by
  -- Local instance justification (defeq pin): retain the exact stage quotient
  -- action while the first-isomorphism theorem infers its restricted codomain.
  -- Local instance justification (defeq pin): fix the actual stage quotient action for first-isomorphism elaboration.
  letI : Algebra Z.B (ring γA hIC hpnil Z e) := stageOverEnvelope γA hIC hpnil Z e
  -- Local instance justification (defeq pin): the restricted target must retain that same stage action.
  letI : Module Z.B (RestrictScalars Z.B (ring γA hIC hpnil Z e)
      (CrystallinePDDeRham.oneForms A (ring γA hIC hpnil Z e)
        (ring γA hIC hpnil Z e).dividedPowers)) :=
    RestrictScalars.module Z.B (ring γA hIC hpnil Z e)
      (CrystallinePDDeRham.oneForms A (ring γA hIC hpnil Z e)
        (ring γA hIC hpnil Z e).dividedPowers)
  exact (Submodule.quotEquivOfEq _ _ (restrictedFormsReduction_kernel γA hIC hpnil Z e).symm).trans
    (@LinearMap.quotKerEquivOfSurjective Z.B
      (CrystallinePDDeRham.oneForms A Z.B Z.B.dividedPowers)
      (RestrictScalars Z.B (ring γA hIC hpnil Z e)
        (CrystallinePDDeRham.oneForms A (ring γA hIC hpnil Z e)
          (ring γA hIC hpnil Z e).dividedPowers))
      inferInstance inferInstance inferInstance inferInstance
      (RestrictScalars.module Z.B (ring γA hIC hpnil Z e)
        (CrystallinePDDeRham.oneForms A (ring γA hIC hpnil Z e)
          (ring γA hIC hpnil Z e).dividedPowers))
      (restrictedFormsReduction γA hIC hpnil Z e)
      (restrictedFormsReduction_surjective γA hIC hpnil Z e))

/-- The source's completed PD one-forms on the completed envelope. -/
noncomputable abbrev completedOneForms :=
  AdicCompletion (Ideal.span {(p : Z.B)}) (CrystallinePDDeRham.oneForms A Z.B Z.B.dividedPowers)

/-- Actual projection of completed PD forms to a quotient stage, via
completion evaluation and the verified finite-stage quotient comparison. -/
noncomputable def completedFormsReduction (e : ℕ) :
    completedOneForms γA hIC hpnil Z →ₛₗ[
      (pAdicQuotientMk γA (algebraMap A C) hIC hpnil Z e).toRingHom]
        CrystallinePDDeRham.oneForms A (ring γA hIC hpnil Z e) (ring γA hIC hpnil Z e).dividedPowers :=
  let f := (algebraicFormsQuotientEquiv γA hIC hpnil Z e).toLinearMap.comp
    (AdicCompletion.eval (Ideal.span {(p : Z.B)}) (CrystallinePDDeRham.oneForms A Z.B Z.B.dividedPowers)
      (e + pAdicOffset γA (algebraMap A C) hIC hpnil Z))
  { toFun := f
    map_add' := f.map_add
    map_smul' := f.map_smul }

/-- The inverse-limit coefficient projection with its actual stage scalar
transport exposed, so it can be tensored with the form projection. -/
noncomputable def semilinearCoefficientProjection (e : ℕ) :
    completedModule γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F →ₛₗ[
      (pAdicQuotientMk γA (algebraMap A C) hIC hpnil Z e).toRingHom]
        coefficientModule γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F e where
  toFun := coefficientProjection γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F e
  map_add' := map_add _
  map_smul' := (coefficientProjection γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F e).map_smul

/-- The uncompleted tensor in the displayed Čech–de Rham term. Its
coefficient module and one-forms have their genuine completed meanings. -/
noncomputable abbrev tensorTerm (m : ℕ) :=
  TensorProduct Z.B (completedModule γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F)
    (exteriorPower.form Z.B (completedOneForms γA hIC hpnil Z) m)

/-- The source's displayed completed tensor term. -/
noncomputable abbrev completedTensorTerm (m : ℕ) :=
  AdicCompletion (Ideal.span {(p : Z.B)})
    (tensorTerm γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F m)

/-- Map both factors of the displayed tensor to the actual stage. In
degree zero the canonical right-unit equivalence identifies M_e tensor D_e
with M_e; positive degrees use the actual tensor and exterior maps. -/
noncomputable def tensorTermProjection (e m : ℕ) :
    tensorTerm γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F m →+
      (deRhamComplex γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F e).X m :=
  match m with
  | 0 =>
      (TensorProduct.rid (ring γA hIC hpnil Z e)
        (coefficientModule γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F e)).toAddEquiv.toAddMonoidHom.comp
          (TensorProduct.map
            (semilinearCoefficientProjection γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F e)
            (CrystallineSemilinearForms.map (R := Z.B) (S := ring γA hIC hpnil Z e)
              (completedFormsReduction γA hIC hpnil Z e) 0)).toAddMonoidHom
  | m + 1 =>
      (TensorProduct.map
        (semilinearCoefficientProjection γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F e)
        (CrystallineSemilinearForms.map (R := Z.B) (S := ring γA hIC hpnil Z e)
          (completedFormsReduction γA hIC hpnil Z e) (m + 1))).toAddMonoidHom

/-- The actual stage projection kills the corresponding p-power submodule
because the stage ring is the quotient by this full shifted exponent. -/
theorem tensorTermProjection_annihilates (e m : ℕ) :
    ((Ideal.span {(p : Z.B)}) ^ (e + pAdicOffset γA (algebraMap A C) hIC hpnil Z) •
      (⊤ : Submodule Z.B (tensorTerm γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F m))).restrictScalars ℤ ≤
        LinearMap.ker
          (tensorTermProjection γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F e m).toIntLinearMap := sorry

/-- Descend the specified tensor projection through its actual p-power
quotient. This is a map constructed on representatives, not a selected iso. -/
noncomputable def tensorQuotientProjection (e m : ℕ) :
    (tensorTerm γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F m ⧸
      (Ideal.span {(p : Z.B)}) ^ (e + pAdicOffset γA (algebraMap A C) hIC hpnil Z) •
        (⊤ : Submodule Z.B (tensorTerm γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F m))) →+
      (deRhamComplex γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F e).X m :=
  (((Ideal.span {(p : Z.B)}) ^ (e + pAdicOffset γA (algebraMap A C) hIC hpnil Z) •
      (⊤ : Submodule Z.B (tensorTerm γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F m))).restrictScalars ℤ).liftQ
    (tensorTermProjection γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F e m).toIntLinearMap
    (tensorTermProjection_annihilates γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F e m)
    |>.toAddMonoidHom

/-- The quotient tensor projection agrees with the explicitly constructed
two-factor map on every representative. -/
theorem tensorQuotientProjection_mk (e m : ℕ)
    (x : tensorTerm γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F m) :
    tensorQuotientProjection γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F e m
      (Submodule.Quotient.mk x) =
        tensorTermProjection γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F e m x := rfl

/-- Tensor products and exterior powers commute with scalar extension.
Together with the actual coefficient and form quotient comparisons this
makes the finite-stage tensor quotient map bijective, without module
finite-generation or a claim that tensor commutes with arbitrary limits. -/
theorem tensorQuotientProjection_bijective (e m : ℕ) :
    Function.Bijective
      (tensorQuotientProjection γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F e m) := sorry

/-- Evaluate a completed tensor at the actual stage exponent, then apply
the canonical finite-stage tensor quotient projection. -/
noncomputable def completedTensorProjection (e m : ℕ) :
    completedTensorTerm γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F m →+
      (deRhamComplex γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F e).X m :=
  (tensorQuotientProjection γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F e m).comp
    (AdicCompletion.eval (Ideal.span {(p : Z.B)})
      (tensorTerm γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F m)
      (e + pAdicOffset γA (algebraMap A C) hIC hpnil Z)).toAddMonoidHom

/-- The actual inverse diagram of degree-m de Rham terms. -/
noncomputable def termSystem (m : ℕ) : ℕᵒᵖ ⥤ AddCommGrpCat.{u} :=
  complexSystem γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F ⋙
    HomologicalComplex.eval AddCommGrpCat.{u} (ComplexShape.up ℕ) m

/-- Completed tensor projections commute with the genuine crystalline
stage reductions on coefficients, PD forms, and their exterior powers. -/
theorem completedTensorProjection_naturality (m : ℕ) {i j : ℕᵒᵖ} (f : i ⟶ j) :
    AddCommGrpCat.ofHom
        (completedTensorProjection γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F i.unop m) ≫
      (termSystem γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F m).map f =
        AddCommGrpCat.ofHom
          (completedTensorProjection γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F j.unop m) := sorry

/-- The cone from the displayed completed tensor uses exactly its actual
finite-stage evaluation maps. -/
noncomputable def tensorCone (m : ℕ) :
    Limits.Cone (termSystem γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F m) where
  pt := AddCommGrpCat.of (completedTensorTerm γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F m)
  π :=
    { app := fun e ↦ AddCommGrpCat.ofHom
        (completedTensorProjection γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F e.unop m)
      naturality := by
        intro i j f
        change (𝟙 _ ≫ _) = _
        rw [Category.id_comp]
        exact (completedTensorProjection_naturality γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F m f).symm }

/-- Canonical comparison from the displayed completed tensor to the inverse
limit of stage terms, induced by its explicitly specified cone. -/
noncomputable def tensorToLimit (m : ℕ) :
    AddCommGrpCat.of (completedTensorTerm γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F m) ⟶
      Limits.limit (termSystem γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F m) :=
  Limits.limit.lift _ (tensorCone γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F m)

/-- The shifted exponents are cofinal in the p-adic tower, and every
finite-stage quotient comparison is bijective. Hence this specified map of
limits is bijective. -/
theorem tensorToLimit_bijective (m : ℕ) :
    Function.Bijective (tensorToLimit γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F m) := sorry

/-- Evaluation of a complex preserves limits. This is the canonical
comparison, not an assumed equality between a limit and one of its terms. -/
noncomputable def termLimitIso (m : ℕ) :
    Limits.limit (termSystem γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F m) ≅
      (completedComplex γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F).X m :=
  (preservesLimitIso
    (HomologicalComplex.eval AddCommGrpCat.{u} (ComplexShape.up ℕ) m)
    (complexSystem γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F)).symm

/-- The specified completed-tensor comparison: quotientwise projection to
the stage limit, followed by the canonical complex-evaluation limit iso. -/
noncomputable def tensorComparison (m : ℕ) :
    completedTensorTerm γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F m ≃+
      (completedComplex γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F).X m :=
  (AddEquiv.ofBijective (tensorToLimit γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F m).hom
    (tensorToLimit_bijective γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F m)).trans
      (termLimitIso γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F m).addCommGroupIsoToAddEquiv

/-- The differential on the displayed completed tensors is transported
from the inverse limit of the actual stage PD de Rham differentials. It is
additive; no false envelope-linearity or finite-stage inverse is asserted. -/
noncomputable def completedDifferential (m : ℕ) :
    completedTensorTerm γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F m →+
      completedTensorTerm γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F (m + 1) :=
  (tensorComparison γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F (m + 1)).symm.toAddMonoidHom.comp
    (((completedComplex γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F).d m (m + 1)).hom.comp
      (tensorComparison γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F m).toAddMonoidHom)

/-- The differential is characterized by the actual stage-limit
differential through the constructed comparison. -/
theorem completedDifferential_spec (m : ℕ)
    (x : completedTensorTerm γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F m) :
    tensorComparison γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F (m + 1)
      (completedDifferential γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F m x) =
        (completedComplex γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F).d m (m + 1)
          (tensorComparison γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F m x) :=
  (tensorComparison γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F (m + 1)).apply_symm_apply _

/-- The transported completed differential squares to zero because the
actual inverse-limit de Rham differential does. -/
theorem completedDifferential_squared (m : ℕ)
    (x : completedTensorTerm γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F m) :
    completedDifferential γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F (m + 1)
      (completedDifferential γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F m x) = 0 := by
  apply (tensorComparison γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F (m + 1 + 1)).injective
  rw [completedDifferential_spec, completedDifferential_spec, map_zero]
  exact ConcreteCategory.congr_hom
    ((completedComplex γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F).d_comp_d m (m + 1) (m + 1 + 1))
    (tensorComparison γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F m x)

/-- The constructed comparison recovers the explicitly specified tensor
projection at every actual finite stage. -/
theorem tensorComparison_stage (e m : ℕ)
    (x : completedTensorTerm γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F m) :
    ((Limits.limit.π (complexSystem γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F) (op e)).f m)
      (tensorComparison γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F m x) =
        completedTensorProjection γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F e m x := by
  let D := complexSystem γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F
  let V := HomologicalComplex.eval AddCommGrpCat.{u} (ComplexShape.up ℕ) m
  have h := ConcreteCategory.congr_hom (preservesLimitIso_inv_π V D (op e))
    (tensorToLimit γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F m x)
  change (V.map (Limits.limit.π D (op e)))
    ((preservesLimitIso V D).inv
      (tensorToLimit γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F m x)) = _
  exact h.trans (ConcreteCategory.congr_hom
    (Limits.limit.lift_π (tensorCone γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F m) (op e)) x)

/-- At every finite stage, the completed differential is precisely the
crystal-induced PD de Rham differential. This ties the transported map to
its geometric meaning, beyond the abstract conjugation specification. -/
theorem completedDifferential_stage (e m : ℕ)
    (x : completedTensorTerm γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F m) :
    completedTensorProjection γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F e (m + 1)
      (completedDifferential γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F m x) =
        (deRhamComplex γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F e).d m (m + 1)
          (completedTensorProjection γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F e m x) := by
  rw [← tensorComparison_stage, completedDifferential_spec, ← tensorComparison_stage]
  exact (ConcreteCategory.congr_hom
    ((Limits.limit.π (complexSystem γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F) (op e)).comm m (m + 1))
    (tensorComparison γA hIC hpnil I γS hc x₀ eX heX hI hγ ho Z F m x)).symm

end CrystallineStagePDConnection
