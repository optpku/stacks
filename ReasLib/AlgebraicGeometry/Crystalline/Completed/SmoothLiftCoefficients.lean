/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import ReasLib.AlgebraicGeometry.Crystalline.SmoothLift.DeRham
public import ReasLib.AlgebraicGeometry.Scheme.Module.AffineSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Differentials.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Sheaf.AffineBasis
public import ReasLib.AlgebraicGeometry.Crystalline.Completed.SmoothLiftStages
public import ReasLib.AlgebraicGeometry.Scheme.Module.DeRham.Connection
public import ReasLib.AlgebraicGeometry.Scheme.Module.DeRham.Reduction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent


@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Crystalline
open CrystallineModuleSheaf CrystallineCoefficients AlgebraicGeometry.Scheme.Modules.DeRham
open DividedPowers.PadicBase
open AlgebraicGeometry.Scheme.Modules.DeRham AlgebraicGeometry.Scheme.Modules.DeRham.Reduction
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Crystalline.Complete

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable [IsAdicComplete (Ideal.span {(p : A)}) A]
variable {IA : Ideal A} (γA : DividedPowers IA)
variable {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A)) [Smooth f]
variable (I : (Spec (.of A)).IdealSheafData)
variable (γS : ∀ V : (Spec (.of A)).affineOpens, DividedPowers (I.ideal V))
variable (hc : ∀ (V : (Spec (.of A)).affineOpens) (a : Γ(Spec (.of A), V)),
  (γS V).IsDPMorphism (γS ((Spec (.of A)).affineBasicOpen a))
    ((Spec (.of A)).presheaf.map (homOfLE ((Spec (.of A)).basicOpen_le a)).op).hom)
variable (hI : AlgebraicGeometry.Scheme.Crystalline.Affine.idealCompatible IA I) (hγ : AlgebraicGeometry.Scheme.Crystalline.Affine.dividedPowersCompatible IA γA I γS)
variable (hpI : IsNilpotent (Ideal.Quotient.mk IA (p : A)))
variable (F : CrisModuleSheaf (Spec (.of A)) I γS hc (smoothLift f I) (smoothLift_x₀ f I))
variable [hcrystal : CrisModuleSheaf.IsCrystal F]
variable [hqc : CrisModuleSheaf.IsLocallyQuasiCoherent F]
section StageIndex

variable (e : ℕ)

/-- The actual chart map from the descended PD base of this stage. -/
noncomputable def stageAffineSectionMap (V : (stageLift γA hpI f e).affineOpens) :
    stageRing γA hpI e →+* Γ(stageLift γA hpI f e, V) :=
  Scheme.Hom.sectionsMap (stageToSpec γA hpI f e) V

/-- Smoothness over the quotient base makes this chart map flat. -/
theorem stageAffineSectionMap_flat (V : (stageLift γA hpI f e).affineOpens) :
    (stageAffineSectionMap γA f hpI e V).Flat :=
  affineSectionMap_flat (stageToSpec γA hpI f e) V

/-- The descended divided powers extend along the genuinely flat stage chart map. -/
theorem stageAffineSectionMap_extendsAlong (V : (stageLift γA hpI f e).affineOpens) :
    (stageRing γA hpI e).dividedPowers.extendsAlong
      (stageAffineSectionMap γA f hpI e V) :=
  DividedPowers.extendsAlong_of_flat (stageRing γA hpI e).dividedPowers
    (stageAffineSectionMap γA f hpI e V) (stageAffineSectionMap_flat γA f hpI e V)

include hI in
/-- The chart ideal is the image of the actual descended base PD ideal. -/
theorem stageAffineSectionMap_map_eq_ker_ideal (V : (stageLift γA hpI f e).affineOpens) :
    (stageRing γA hpI e).ideal.map (stageAffineSectionMap γA f hpI e V) =
      (stageInclusion γA hpI f e I hI).ker.ideal V := sorry

/-- First descend the base PD structure, then extend it along the smooth chart. -/
noncomputable def stageDividedPowers (V : (stageLift γA hpI f e).affineOpens) :
    DividedPowers ((stageInclusion γA hpI f e I hI).ker.ideal V) :=
  DividedPowers.dividedPowers_ofIdealEq
    (stageAffineSectionMap_map_eq_ker_ideal γA f I hI hpI e V)
    (DividedPowers.extensionAlong (stageRing γA hpI e).dividedPowers
      (stageAffineSectionMap γA f hpI e V)
      (stageAffineSectionMap_extendsAlong γA f hpI e V)).dividedPowers

/-- The affine stage structure map is the quotient followed by its smooth chart map. -/
theorem stageAffineSectionMap_comp_quotient (V : (stageLift γA hpI f e).affineOpens) :
    (stageAffineSectionMap γA f hpI e V).comp (quotient γA hpI e).toRingHom =
      Scheme.Hom.sectionsMap (stageToY γA hpI f e ≫ f) V := sorry

/-- Compatibility of the extended divided powers on basic opens of `Y_e`. -/
theorem stageDividedPowers_compatible (V : (stageLift γA hpI f e).affineOpens)
    (a : Γ(stageLift γA hpI f e, V)) :
    (stageDividedPowers γA f I hI hpI e V).IsDPMorphism
      (stageDividedPowers γA f I hI hpI e ((stageLift γA hpI f e).affineBasicOpen a))
      ((stageLift γA hpI f e).presheaf.map
        (homOfLE ((stageLift γA hpI f e).basicOpen_le a)).op).hom :=
  sorry

/-- The kernel ideal of `X ⟶ Y_e` with the uniquely extended divided powers is a
divided-power thickening. -/
theorem stageIdeal_thickening :
    IsDividedPowerThickening (stageLift γA hpI f e) (stageInclusion γA hpI f e I hI).ker
      (stageDividedPowers γA f I hI hpI e) (stageDividedPowers_compatible γA f I hI hpI e) :=
  sorry

/-- The closed-fibre inclusion `X ⟶ Y_e` is a thickening. -/
instance stageInclusion_isThickening :
    IsThickening (stageInclusion γA hpI f e I hI) :=
  sorry

/-- The closed-fibre inclusion of a stage is a closed immersion. -/
instance stageInclusion_isClosedImmersion :
    IsClosedImmersion (stageInclusion γA hpI f e I hI) :=
  sorry

/-- The actual `p`-power-stage crystalline object over `Spec A`. Its thickening is
`Y_e`, and the source is the identity on the original closed fibre. -/
noncomputable def stageObject :
    CrystallineObject (Spec (.of A)) I γS hc (smoothLift f I) (smoothLift_x₀ f I) where
  source := Over.mk (𝟙 (smoothLift f I))
  thickening := stageLift γA hpI f e
  thickeningToBase := stageToY γA hpI f e ≫ f
  inclusion := stageInclusion γA hpI f e I hI
  ideal := (stageInclusion γA hpI f e I hI).ker
  gamma := stageDividedPowers γA f I hI hpI e
  thickening_compatible := stageDividedPowers_compatible γA f I hI hpI e
  isThickening := stageIdeal_thickening γA f I hI hpI e
  inclusion_isThickening := stageInclusion_isThickening γA f I hI hpI e
  ideal_eq_ker := rfl
  source_comm := by
    change stageInclusion γA hpI f e I hI ≫ (stageToY γA hpI f e ≫ f) =
      𝟙 _ ≫ smoothLift_x₀ f I ≫ I.subschemeι
    rw [← Category.assoc, stageInclusion_comp γA hpI f e I hI, Category.id_comp]
    exact pullback.condition

include hγ in
/-- The stage object extends the specified base divided-power structure. -/
theorem stageObject_baseCompatible :
    CrystallineBaseCompatible I γS hc (smoothLift_x₀ f I)
      (stageObject γA f I γS hc hI hpI e) :=
  sorry

/-- The identity on the closed fibre is open, so the stage object lies in the
small crystalline site. -/
noncomputable def stageSmallObject :
    smallCrystallineSite (Spec (.of A)) I γS hc
      (smoothLift f I) (smoothLift_x₀ f I) where
  obj := ⟨stageObject γA f I γS hc hI hpI e,
    stageObject_baseCompatible γA f I γS hc hI hγ hpI e⟩
  property := by
    change IsOpenImmersion (𝟙 (smoothLift f I))
    infer_instance


/-- The crystalline coefficient module on `Y_e`, obtained by evaluating the
crystal at the actual `p`-power-stage thickening. -/
noncomputable def stageCoefficient : (stageLift γA hpI f e).Modules :=
  F.obj (stageSmallObject γA f I γS hc hI hγ hpI e)

include hqc in
/-- Finite type of the crystal implies coherence of each stage coefficient. -/
theorem stageCoefficient_isCoherent [IsNoetherianRing A]
    (hft : ∀ Aobj, (F.obj Aobj).IsFiniteType) :
    (stageCoefficient γA f I γS hc hI hγ hpI F e).IsCoherent :=
  sorry

variable (U : (stageLift γA hpI f e).affineOpens)

/-- The algebra on stage affine-chart functions is induced by `Y_e ⟶ Spec A`. -/
noncomputable abbrev stageChartAlgebra : Algebra A Γ(stageLift γA hpI f e, U.1) :=
  (Scheme.Hom.sectionsMap (stageToY γA hpI f e ≫ f) U).toAlgebra

/-- The quotient closed-fibre chart of an affine open of `Y_e`. -/
noncomputable def stageFibre :
    Spec (.of (Γ(stageLift γA hpI f e, U.1) ⧸ (stageInclusion γA hpI f e I hI).ker.ideal U)) ⟶
      smoothLift f I :=
  (stageInclusion γA hpI f e I hI).ker.subschemeCover.f U ≫
    inv (stageInclusion γA hpI f e I hI).toImage

/-- The canonical quotient-chart map is open in the actual closed fibre. -/
theorem stageFibre_open : IsOpenImmersion (stageFibre γA f I hI hpI e U) :=
  sorry

/-- The affine chart square of a stage commutes with the base and closed-fibre maps. -/
theorem stageSquare :
    Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk ((stageInclusion γA hpI f e I hI).ker.ideal U))) ≫
      Spec.map (CommRingCat.ofHom (Scheme.Hom.sectionsMap (stageToY γA hpI f e ≫ f) U)) =
      stageFibre γA f I hI hpI e U ≫ smoothLift_x₀ f I ≫ I.subschemeι :=
  sorry

/-- The affine PD ideal of `X` in an open of `Y_e` is nil, using nilpotence of
`p` in `A / I` together with the stable p-power exponent on the stage. -/
theorem stageIdeal_nil :
    ∀ x ∈ (stageInclusion γA hpI f e I hI).ker.ideal U, IsNilpotent x :=
  sorry

/-- The affine chart of a stage as a crystalline object over the original closed fibre. -/
noncomputable def stageAffineObject :
    CrystallineObject (Spec (.of A)) I γS hc (smoothLift f I) (smoothLift_x₀ f I) :=
  CechCrisCover.affineCrystallineObject I γS hc (smoothLift_x₀ f I)
    ((stageInclusion γA hpI f e I hI).ker.ideal U) (stageDividedPowers γA f I hI hpI e U)
    (stageIdeal_nil γA f I hI hpI e U)
    (Spec.map (CommRingCat.ofHom (Scheme.Hom.sectionsMap (stageToY γA hpI f e ≫ f) U)))
    (stageFibre γA f I hI hpI e U) (stageSquare γA f I hI hpI e U)

include hγ in
/-- The affine stage chart agrees with the specified base divided-power structure. -/
theorem stageAffineObject_baseCompatible :
    CrystallineBaseCompatible I γS hc (smoothLift_x₀ f I)
      (stageAffineObject γA f I γS hc hI hpI e U) :=
  sorry



/-- The affine PD de Rham complex of a stage chart. -/
noncomputable def stageComplex :=
  -- Local instance justification (noncanonical choice): the stage structure map fixes this chart's A-algebra action.
  letI : Algebra A Γ(stageLift γA hpI f e, U.1) := stageChartAlgebra γA f hpI e U
  CrystallinePDSquareZeroGeometry.deRhamComplex A Γ(stageLift γA hpI f e, U.1)
    (stageDividedPowers γA f I hI hpI e U) I γS hc (smoothLift_x₀ f I)
    (Spec.map (CommRingCat.ofHom (Scheme.Hom.sectionsMap (stageToY γA hpI f e ≫ f) U)))
    (stageFibre γA f I hI hpI e U) (stageSquare γA f I hI hpI e U)
    (stageIdeal_nil γA f I hI hpI e U)
    (stageAffineObject_baseCompatible γA f I γS hc hI hγ hpI e U)
    (stageFibre_open γA f I hI hpI e U)
    (CrystallinePDSquareZeroGeometry.differentialLift_overAffineBase A
      Γ(stageLift γA hpI f e, U.1) (stageDividedPowers γA f I hI hpI e U)) F

/-- The actual affine chart map `Spec Γ(Y_e, U) ⟶ Y_e`. -/
noncomputable def stageChart : Spec (.of Γ(stageLift γA hpI f e, U.1)) ⟶ stageLift γA hpI f e :=
  U.property.isoSpec.inv ≫ U.1.ι

/-- The affine chart as an object of the small crystalline site. -/
noncomputable def stageAffineSmallObject :
    smallCrystallineSite (Spec (.of A)) I γS hc
      (smoothLift f I) (smoothLift_x₀ f I) where
  obj := ⟨stageAffineObject γA f I γS hc hI hpI e U,
    stageAffineObject_baseCompatible γA f I γS hc hI hγ hpI e U⟩
  property := stageFibre_open γA f I hI hpI e U

/-- The affine closed-fibre chart is a morphism over the closed fibre. -/
theorem stageAffineToWhole_over :
    stageFibre γA f I hI hpI e U ≫ (stageObject γA f I γS hc hI hpI e).source.hom = (stageAffineObject γA f I γS hc hI hpI e U).source.hom := sorry

/-- The affine chart square commutes with the stage inclusion. -/
theorem stageAffineToWhole_source_comm :
    stageFibre γA f I hI hpI e U ≫ (stageObject γA f I γS hc hI hpI e).inclusion = (stageAffineObject γA f I γS hc hI hpI e U).inclusion ≫ stageChart γA f hpI e U := sorry

/-- The affine chart morphism commutes with the base structure morphism. -/
theorem stageAffineToWhole_base_comm :
    stageChart γA f hpI e U ≫ (stageObject γA f I γS hc hI hpI e).thickeningToBase = (stageAffineObject γA f I γS hc hI hpI e U).thickeningToBase := sorry

/-- The affine chart pulls back the stage ideal into its chart ideal. -/
theorem stageAffineToWhole_ideal_compatible :
    (stageObject γA f I γS hc hI hpI e).ideal.comap (stageChart γA f hpI e U) ≤ (stageAffineObject γA f I γS hc hI hpI e U).ideal := sorry

/-- The affine chart morphism preserves the stage divided powers. -/
theorem stageAffineToWhole_dividedPowers_compatible :
    ∀ (V : (stageObject γA f I γS hc hI hpI e).thickening.affineOpens) (W : (stageAffineObject γA f I γS hc hI hpI e U).thickening.affineOpens)
      (hVW : W.1 ≤ (stageChart γA f hpI e U) ⁻¹ᵁ V.1),
    ((stageObject γA f I γS hc hI hpI e).gamma V).IsDPMorphism ((stageAffineObject γA f I γS hc hI hpI e U).gamma W)
      ((stageChart γA f hpI e U).appLE V.1 W.1 hVW).hom := sorry

/-- The actual affine representative maps to the whole stage object. -/
noncomputable def stageAffineToWhole :
    stageAffineSmallObject γA f I γS hc hI hγ hpI e U ⟶
      stageSmallObject γA f I γS hc hI hγ hpI e :=
  ObjectProperty.homMk
    { source := Over.homMk (stageFibre γA f I hI hpI e U)
        (stageAffineToWhole_over γA f I γS hc hI hpI e U)
      thickening := stageChart γA f hpI e U
      source_comm := stageAffineToWhole_source_comm γA f I γS hc hI hpI e U
      base_comm := stageAffineToWhole_base_comm γA f I γS hc hI hpI e U
      ideal_compatible := stageAffineToWhole_ideal_compatible γA f I γS hc hI hpI e U
      dividedPowers_compatible := stageAffineToWhole_dividedPowers_compatible γA f I γS hc hI hpI e U }

/-- The crystal comparison on the stage affine chart. -/
noncomputable def stageCoefficientIso :
    (Scheme.Modules.pullback (stageChart γA f hpI e U)).obj
        (stageCoefficient γA f I γS hc hI hγ hpI F e) ≅
      F.obj (stageAffineSmallObject γA f I γS hc hI hγ hpI e U) :=
  @asIso _ _ _ _ (F.comparison (stageAffineToWhole γA f I γS hc hI hγ hpI e U))
    (CrystallineModuleSheaf.ModuleSheaf.IsCrystal.comparison_isIso _)

/-- Affine sections of the stage coefficient identify with the affine crystal
coefficient. -/
noncomputable def stageCoefficientSectionsIso :
    (stageCoefficient γA f I γS hc hI hγ hpI F e).presheaf.obj (op U.1) ≅
      (F.obj (stageAffineSmallObject γA f I γS hc hI hγ hpI e U)).presheaf.obj (op ⊤) :=
  AlgebraicGeometry.Scheme.Modules.Affine.pullbackSectionsIso U
      (stageCoefficient γA f I γS hc hI hγ hpI F e) ≪≫
    ((Scheme.Modules.toPresheaf _).mapIso
      (stageCoefficientIso γA f I γS hc hI hγ hpI F e U)).app (op ⊤)

/-- The genuine affine crystal coefficient of a stage chart. -/
noncomputable def stageCoefficientModule : ModuleCat.{u} Γ(stageLift γA hpI f e, U.1) :=
  (ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of Γ(stageLift γA hpI f e, U.1))).inv.hom).obj
    ((F.obj (stageAffineSmallObject γA f I γS hc hI hγ hpI e U)).val.obj (op ⊤))

/-- The affine coefficient comparison respects the chart scalar action. -/
theorem stageCoefficientSectionsEquiv_smul :
    let g : Γ(stageCoefficient γA f I γS hc hI hγ hpI F e, U.1) →
        stageCoefficientModule γA f I γS hc hI hγ hpI F e U :=
      (stageCoefficientSectionsIso γA f I γS hc hI hγ hpI F e U).addCommGroupIsoToAddEquiv
    ∀ (a : Γ(stageLift γA hpI f e, U.1))
      (m : Γ(stageCoefficient γA f I γS hc hI hγ hpI F e, U.1)),
      g (a • m) = a • g m := sorry

/-- The canonical coefficient comparison as a linear equivalence. -/
noncomputable def stageCoefficientSectionsEquiv :
    Γ(stageCoefficient γA f I γS hc hI hγ hpI F e, U.1) ≃ₗ[Γ(stageLift γA hpI f e, U.1)]
      stageCoefficientModule γA f I γS hc hI hγ hpI F e U where
  __ := (stageCoefficientSectionsIso γA f I γS hc hI hγ hpI F e U).addCommGroupIsoToAddEquiv
  map_smul' := stageCoefficientSectionsEquiv_smul γA f I γS hc hI hγ hpI F e U

/-- PD relations vanish on a smooth stage chart. -/
theorem stagePDRelations_eq_bot :
    -- Local instance justification (noncanonical choice): the stage structure map fixes this chart algebra.
    letI : Algebra A Γ(stageLift γA hpI f e, U.1) := stageChartAlgebra γA f hpI e U
    CrystallinePDDeRham.relations A Γ(stageLift γA hpI f e, U.1)
      (stageDividedPowers γA f I hI hpI e U) = ⊥ :=
  sorry

/-- The PD quotient on a stage chart is identified with ordinary Kähler differentials. -/
noncomputable def stagePDToOrdinary :=
  -- Local instance justification (noncanonical choice): the stage structure map fixes this chart algebra.
  letI : Algebra A Γ(stageLift γA hpI f e, U.1) := stageChartAlgebra γA f hpI e U
  Submodule.quotEquivOfEqBot _ (stagePDRelations_eq_bot γA f I hI hpI e U)

/-- Canonical comparison of PD one-forms with sheaf one-forms on a stage chart. -/
noncomputable def stagePDFormsComparison :=
  -- Local instance justification (noncanonical choice): the stage structure map fixes this chart algebra.
  letI : Algebra A Γ(stageLift γA hpI f e, U.1) := stageChartAlgebra γA f hpI e U
  (AlgebraicGeometry.Scheme.RelativeDifferentials.Affine.comparison (stageToY γA hpI f e ≫ f) U).comp
    (stagePDToOrdinary γA f I hI hpI e U).toLinearMap

/-- Bijectivity of the stage PD-form comparison. -/
theorem stagePDFormsComparison_bijective :
    Function.Bijective (stagePDFormsComparison γA f I hI hpI e U) :=
  sorry

/-- The uniquely specified stage PD-form/sheaf-section equivalence. -/
noncomputable def stagePDFormsEquiv :=
  LinearEquiv.ofBijective (stagePDFormsComparison γA f I hI hpI e U)
    (stagePDFormsComparison_bijective γA f I hI hpI e U)

/-- Algebraic tensors with PD forms compared to sheaf de Rham terms. -/
noncomputable def stageTensorToSections (n : ℕ) :=
  -- Local instance justification (noncanonical choice): this chart uses the A-action of the stage structure map.
  letI : Algebra A Γ(stageLift γA hpI f e, U.1) := stageChartAlgebra γA f hpI e U
  (AlgebraicGeometry.Scheme.Modules.Affine.tensorMap U
    (stageCoefficient γA f I γS hc hI hγ hpI F e)
    (forms (stageToY γA hpI f e ≫ f) n)).comp
      (TensorProduct.map
        (stageCoefficientSectionsEquiv γA f I γS hc hI hγ hpI F e U).symm.toLinearMap
        ((AlgebraicGeometry.Scheme.Modules.Affine.exteriorMap U
          (oneForms (stageToY γA hpI f e ≫ f)) n).comp
            (exteriorPower.form.map (stagePDFormsEquiv γA f I hI hpI e U).toLinearMap n)))

include hqc in
/-- Affine quasi-coherence makes the tensor/sheafification comparison bijective. -/
theorem stageTensorToSections_bijective (n : ℕ) :
    Function.Bijective (stageTensorToSections γA f I γS hc hI hγ hpI F e U n) :=
  sorry

/-- The canonical affine tensor comparison as a linear equivalence. -/
noncomputable def stageTensorSectionsEquiv (n : ℕ) :=
  LinearEquiv.ofBijective (stageTensorToSections γA f I γS hc hI hγ hpI F e U n)
    (stageTensorToSections_bijective γA f I γS hc hI hγ hpI F e U n)

/-- Affine de Rham terms identify with sections of the sheaf terms. -/
noncomputable def stageTermSectionsEquiv (n : ℕ) :
    (stageComplex γA f I γS hc hI hγ hpI F e U).X n ≃+
      Γ(term (stageToY γA hpI f e ≫ f)
        (stageCoefficient γA f I γS hc hI hγ hpI F e) n, U.1) :=
  match n with
  | 0 =>
      (TensorProduct.rid Γ(stageLift γA hpI f e, U.1)
          (stageCoefficientModule γA f I γS hc hI hγ hpI F e U)).symm.toAddEquiv.trans
        (stageTensorSectionsEquiv γA f I γS hc hI hγ hpI F e U 0).toAddEquiv
  | n + 1 => (stageTensorSectionsEquiv γA f I γS hc hI hγ hpI F e U (n + 1)).toAddEquiv

/-- Local de Rham differentiation on sheaf sections of a stage chart. -/
noncomputable def stageLocalDifferential (n : ℕ) :
    Γ(term (stageToY γA hpI f e ≫ f)
        (stageCoefficient γA f I γS hc hI hγ hpI F e) n, U.1) →+
      Γ(term (stageToY γA hpI f e ≫ f)
        (stageCoefficient γA f I γS hc hI hγ hpI F e) (n + 1), U.1) :=
  (stageTermSectionsEquiv γA f I γS hc hI hγ hpI F e U (n + 1)).toAddMonoidHom.comp
    (((stageComplex γA f I γS hc hI hγ hpI F e U).d n (n + 1)).hom.comp
      (stageTermSectionsEquiv γA f I γS hc hI hγ hpI F e U n).symm.toAddMonoidHom)

/-- The stage sheaf term with scalars restricted to `A`. -/
noncomputable abbrev stageSheafTerm (n : ℕ) :=
  baseTerm (stageToY γA hpI f e ≫ f) (stageCoefficient γA f I γS hc hI hγ hpI F e) n

/-- The stage local differential respects the original base-ring scalar action. -/
theorem stageLocalDifferential_smul (n : ℕ) :
    let d : (stageSheafTerm γA f I γS hc hI hγ hpI F e n).obj.obj (op U.1) →
        (stageSheafTerm γA f I γS hc hI hγ hpI F e (n + 1)).obj.obj (op U.1) :=
      stageLocalDifferential γA f I γS hc hI hγ hpI F e U n
    ∀ (a : A) (m : (stageSheafTerm γA f I γS hc hI hγ hpI F e n).obj.obj (op U.1)),
      d (a • m) = a • d m := sorry

/-- The local geometric differential is A-linear. -/
noncomputable def stageLocalLinearDifferential (n : ℕ) :
    (stageSheafTerm γA f I γS hc hI hγ hpI F e n).obj.obj (op U.1) ⟶
      (stageSheafTerm γA f I γS hc hI hγ hpI F e (n + 1)).obj.obj (op U.1) :=
  let source := (stageSheafTerm γA f I γS hc hI hγ hpI F e n).obj.obj (op U.1)
  let target := (stageSheafTerm γA f I γS hc hI hγ hpI F e (n + 1)).obj.obj (op U.1)
  @ModuleCat.ofHom A _ source target source.isAddCommGroup source.isModule
    target.isAddCommGroup target.isModule
    { toFun := stageLocalDifferential γA f I γS hc hI hγ hpI F e U n
      map_add' := map_add _
      map_smul' := stageLocalDifferential_smul γA f I γS hc hI hγ hpI F e U n }

/-- The stage affine differentials commute with affine-open restriction. -/
theorem stageBasisDifferential_naturality (n : ℕ)
    {V W : (InducedCategory (stageLift γA hpI f e).Opens
      (fun U : (stageLift γA hpI f e).affineOpens ↦ U.1))ᵒᵖ} (i : V ⟶ W) :
    ((AlgebraicGeometry.Scheme.AffineSheaf.affineInclusion (stageLift γA hpI f e)).op ⋙
      (stageSheafTerm γA f I γS hc hI hγ hpI F e n).obj).map i ≫
        stageLocalLinearDifferential γA f I γS hc hI hγ hpI F e W.unop n =
      stageLocalLinearDifferential γA f I γS hc hI hγ hpI F e V.unop n ≫
        ((AlgebraicGeometry.Scheme.AffineSheaf.affineInclusion (stageLift γA hpI f e)).op ⋙
          (stageSheafTerm γA f I γS hc hI hγ hpI F e (n + 1)).obj).map i := sorry

/-- Affine components of the stage sheaf differential. -/
noncomputable def stageBasisDifferential (n : ℕ) :
    (AlgebraicGeometry.Scheme.AffineSheaf.affineInclusion (stageLift γA hpI f e)).op ⋙
        (stageSheafTerm γA f I γS hc hI hγ hpI F e n).obj ⟶
      (AlgebraicGeometry.Scheme.AffineSheaf.affineInclusion (stageLift γA hpI f e)).op ⋙
        (stageSheafTerm γA f I γS hc hI hγ hpI F e (n + 1)).obj where
  app V := stageLocalLinearDifferential γA f I γS hc hI hγ hpI F e V.unop n
  naturality := fun _ _ i ↦
    stageBasisDifferential_naturality γA f I γS hc hI hγ hpI F e n i

/-- The actual sheaf-level A-linear differential of the stage coefficient. -/
noncomputable def stageSheafDifferential (n : ℕ) :
    stageSheafTerm γA f I γS hc hI hγ hpI F e n ⟶
      stageSheafTerm γA f I γS hc hI hγ hpI F e (n + 1) :=
  AlgebraicGeometry.Scheme.AffineSheaf.extend (stageLift γA hpI f e) _ _
    (stageBasisDifferential γA f I γS hc hI hγ hpI F e n)

/-- The crystalline connection on the stage coefficient, obtained by uniquely
extending the affine PD connections of the crystal. -/
noncomputable def stageConnection :
    asBaseSheaf (stageToY γA hpI f e ≫ f)
      (stageCoefficient γA f I γS hc hI hγ hpI F e) ⟶
      asBaseSheaf (stageToY γA hpI f e ≫ f)
        (oneFormTensor (stageToY γA hpI f e ≫ f)
          (stageCoefficient γA f I γS hc hI hγ hpI F e)) :=
  (AlgebraicGeometry.Scheme.Modules.DeRham.baseDegreeZero (stageToY γA hpI f e ≫ f)
      (stageCoefficient γA f I γS hc hI hγ hpI F e)).inv ≫
    stageSheafDifferential γA f I γS hc hI hγ hpI F e 0 ≫
      (AlgebraicGeometry.Scheme.Modules.DeRham.baseDegreeOne (stageToY γA hpI f e ≫ f)
        (stageCoefficient γA f I γS hc hI hγ hpI F e)).hom

/-- The crystalline stage connection satisfies the sheaf Leibniz law. -/
theorem stageConnection_isConnection :
    IsConnection (stageToY γA hpI f e ≫ f)
      (stageCoefficient γA f I γS hc hI hγ hpI F e)
      (stageConnection γA f I γS hc hI hγ hpI F e) :=
  sorry

/-- The PD connection of a stage chart is integrable. -/
theorem stageConnection_integrable :
    stageConnection γA f I γS hc hI hγ hpI F e ≫
      (AlgebraicGeometry.Scheme.Modules.DeRham.baseDegreeOne (stageToY γA hpI f e ≫ f)
        (stageCoefficient γA f I γS hc hI hγ hpI F e)).inv ≫
      stageSheafDifferential γA f I γS hc hI hγ hpI F e 1 = 0 :=
  sorry

/-- The stage transition fixes the closed fibre inclusion. -/
theorem stageObjectStep_source_comm :
    𝟙 (smoothLift f I) ≫ (stageObject γA f I γS hc hI hpI (e + 1)).inclusion = (stageObject γA f I γS hc hI hpI e).inclusion ≫ stageStep γA hpI f e := sorry

/-- The stage transition commutes with the base structure morphisms. -/
theorem stageObjectStep_base_comm :
    stageStep γA hpI f e ≫ (stageObject γA f I γS hc hI hpI (e + 1)).thickeningToBase = (stageObject γA f I γS hc hI hpI e).thickeningToBase := sorry

/-- The stage transition pulls the larger-stage ideal into the smaller-stage ideal. -/
theorem stageObjectStep_ideal_compatible :
    (stageObject γA f I γS hc hI hpI (e + 1)).ideal.comap (stageStep γA hpI f e) ≤ (stageObject γA f I γS hc hI hpI e).ideal := sorry

/-- The stage transition preserves the descended divided powers. -/
theorem stageObjectStep_dividedPowers_compatible :
    ∀ (V : (stageObject γA f I γS hc hI hpI (e + 1)).thickening.affineOpens) (W : (stageObject γA f I γS hc hI hpI e).thickening.affineOpens)
      (hVW : W.1 ≤ (stageStep γA hpI f e) ⁻¹ᵁ V.1),
    ((stageObject γA f I γS hc hI hpI (e + 1)).gamma V).IsDPMorphism ((stageObject γA f I γS hc hI hpI e).gamma W)
      ((stageStep γA hpI f e).appLE V.1 W.1 hVW).hom := sorry

/-- The actual crystalline transition fixes the original closed fibre and
uses the spectrum of the stable quotient transition on the thickenings. -/
noncomputable def stageObjectStep :
    CrystallineObject.Hom (stageObject γA f I γS hc hI hpI e)
      (stageObject γA f I γS hc hI hpI (e + 1)) where
  source := 𝟙 _
  thickening := stageStep γA hpI f e
  source_comm := stageObjectStep_source_comm γA f I γS hc hI hpI e
  base_comm := stageObjectStep_base_comm γA f I γS hc hI hpI e
  ideal_compatible := stageObjectStep_ideal_compatible γA f I γS hc hI hpI e
  dividedPowers_compatible := stageObjectStep_dividedPowers_compatible γA f I γS hc hI hpI e

/-- Restrict the specified transition to the small crystalline category. -/
noncomputable def stageSmallStep :
    stageSmallObject γA f I γS hc hI hγ hpI e ⟶
      stageSmallObject γA f I γS hc hI hγ hpI (e + 1) :=
  ObjectProperty.homMk (stageObjectStep γA f I γS hc hI hpI e)

/-- The stage coefficient transition is precisely the crystal comparison,
not a chosen isomorphism between the coefficient modules. -/
noncomputable def stageCoefficientStep :
    (Scheme.Modules.pullback (stageStep γA hpI f e)).obj
        (stageCoefficient γA f I γS hc hI hγ hpI F (e + 1)) ≅
      stageCoefficient γA f I γS hc hI hγ hpI F e :=
  @asIso _ _ _ _ (F.comparison (stageSmallStep γA f I γS hc hI hγ hpI e))
    (CrystallineModuleSheaf.ModuleSheaf.IsCrystal.comparison_isIso _)

/-- The forward coefficient transition retains the supplied crystal's map. -/
theorem stageCoefficientStep_hom :
    (stageCoefficientStep γA f I γS hc hI hγ hpI F e).hom =
      F.comparison (stageSmallStep γA f I γS hc hI hγ hpI e) := rfl

end StageIndex

/-- Canonical identification between an iterated pullback to the smaller stage
and the direct pullback of an algebraized module. -/
noncomputable def reductionStep (FY : Y.Modules) (e : ℕ) :
    (Scheme.Modules.pullback (stageStep γA hpI f e)).obj
        ((Scheme.Modules.pullback (stageToY γA hpI f (e + 1))).obj FY) ≅
      (Scheme.Modules.pullback (stageToY γA hpI f e)).obj FY :=
  (Scheme.Modules.pullbackComp (stageStep γA hpI f e)
      (stageToY γA hpI f (e + 1))).app FY ≪≫
    (Scheme.Modules.pullbackCongr (stageStep_toY γA hpI f e)).app FY


/-- Compatible horizontal identifications with the genuine crystalline stage
coefficients. The index runs through a cofinal PD-stable tail e+N.
The coefficient isomorphisms may be chosen by algebraization; the quotient,
tensor, differential, and transition maps are fixed canonical constructions. -/
structure ReductionSystem (FY : Y.Modules)
    (nabla : asBaseSheaf f FY ⟶ asBaseSheaf f (oneFormTensor f FY)) where
  /-- The module quotient on each stage identifies with the crystal evaluation. -/
  coefficientIso (e : ℕ) :
    (Scheme.Modules.pullback (stageToY γA hpI f e)).obj FY ≅
      stageCoefficient γA f I γS hc hI hγ hpI F e
  /-- The same coefficient map induces the comparison of connection targets. -/
  horizontal (e : ℕ) :
    IsHorizontal f (stageToY γA hpI f e) FY
      (stageCoefficient γA f I γS hc hI hγ hpI F e) nabla
      (stageConnection γA f I γS hc hI hγ hpI F e) (coefficientIso e).hom
  /-- Identifications commute with the actual crystal restriction isomorphisms. -/
  compatible (e : ℕ) :
    (Scheme.Modules.pullback (stageStep γA hpI f e)).map (coefficientIso (e + 1)).hom ≫
        (stageCoefficientStep γA f I γS hc hI hγ hpI F e).hom =
      (reductionStep γA f hpI FY e).hom ≫ (coefficientIso e).hom

/-- Packages given coefficient identifications, horizontality, and transition
compatibility into a reduction system. -/
noncomputable def ReductionSystem.ofIsos (FY : Y.Modules)
    (nabla : asBaseSheaf f FY ⟶ asBaseSheaf f (oneFormTensor f FY))
    (coefficientIso : ∀ e : ℕ,
      (Scheme.Modules.pullback (stageToY γA hpI f e)).obj FY ≅
        stageCoefficient γA f I γS hc hI hγ hpI F e)
    (horizontal : ∀ e : ℕ,
      IsHorizontal f (stageToY γA hpI f e) FY
        (stageCoefficient γA f I γS hc hI hγ hpI F e) nabla
        (stageConnection γA f I γS hc hI hγ hpI F e) (coefficientIso e).hom)
    (compatible : ∀ e : ℕ,
      (Scheme.Modules.pullback (stageStep γA hpI f e)).map (coefficientIso (e + 1)).hom ≫
          (stageCoefficientStep γA f I γS hc hI hγ hpI F e).hom =
        (reductionStep γA f hpI FY e).hom ≫ (coefficientIso e).hom) :
    ReductionSystem γA f I γS hc hI hγ hpI F FY nabla where
  coefficientIso := coefficientIso
  horizontal := horizontal
  compatible := compatible

/-- The constructor retains the given family of coefficient identifications. -/
theorem ReductionSystem.ofIsos_coefficientIso (FY : Y.Modules)
    (nabla : asBaseSheaf f FY ⟶ asBaseSheaf f (oneFormTensor f FY))
    (coefficientIso : ∀ e : ℕ,
      (Scheme.Modules.pullback (stageToY γA hpI f e)).obj FY ≅
        stageCoefficient γA f I γS hc hI hγ hpI F e)
    (horizontal : ∀ e : ℕ,
      IsHorizontal f (stageToY γA hpI f e) FY
        (stageCoefficient γA f I γS hc hI hγ hpI F e) nabla
        (stageConnection γA f I γS hc hI hγ hpI F e) (coefficientIso e).hom)
    (compatible : ∀ e : ℕ,
      (Scheme.Modules.pullback (stageStep γA hpI f e)).map (coefficientIso (e + 1)).hom ≫
          (stageCoefficientStep γA f I γS hc hI hγ hpI F e).hom =
        (reductionStep γA f hpI FY e).hom ≫ (coefficientIso e).hom) :
    (ReductionSystem.ofIsos γA f I γS hc hI hγ hpI F FY nabla
        coefficientIso horizontal compatible).coefficientIso =
      coefficientIso :=
  sorry

/-- A reduction system supplies coefficient identifications, horizontality of
those identifications, and compatibility with crystalline transitions. -/
theorem ReductionSystem.spec {FY : Y.Modules}
    {nabla : asBaseSheaf f FY ⟶ asBaseSheaf f (oneFormTensor f FY)}
    (hred : ReductionSystem γA f I γS hc hI hγ hpI F FY nabla) (e : ℕ) :
    IsHorizontal f (stageToY γA hpI f e) FY
        (stageCoefficient γA f I γS hc hI hγ hpI F e) nabla
        (stageConnection γA f I γS hc hI hγ hpI F e) (hred.coefficientIso e).hom ∧
      ((Scheme.Modules.pullback (stageStep γA hpI f e)).map
            (hred.coefficientIso (e + 1)).hom ≫
          (stageCoefficientStep γA f I γS hc hI hγ hpI F e).hom =
        (reductionStep γA f hpI FY e).hom ≫ (hred.coefficientIso e).hom) :=
  sorry

end AlgebraicGeometry.Scheme.Crystalline.Complete
