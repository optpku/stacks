/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import stacks_project.Chap60.Remark_60_24_11_Comparison_AffineGeometry
public import stacks_project.Chap60.Remark_60_24_11_Comparison_AffineSections
public import stacks_project.Chap60.Remark_60_24_11_Comparison_AffineSheafExtension
public import stacks_project.Chap60.Remark_60_24_11_Comparison_SheafDegreeBridges
public import stacks_project.Chap60.Remark_60_24_14_Complete_comparison_Geometry
public import stacks_project.Chap60.Remark_60_24_14_Complete_comparison_ConnectionReduction
public import stacks_project.Chap60.Remark_60_24_14_Complete_comparison_DeRham
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Crystalline
open CrystallineModuleSheaf CrystallineCoefficients CrystallineSmoothLiftTerms
open CrystallineCompleteStableBase
open CrystallineCompleteConnection CrystallineCompleteReduction
open scoped TensorProduct

universe u

namespace CrystallineCompleteStages

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable [IsAdicComplete (Ideal.span {(p : A)}) A]
variable {IA : Ideal A} (γA : DividedPowers IA)
variable {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A)) [Smooth f]
variable (I : (Spec (.of A)).IdealSheafData)
variable (γS : ∀ V : (Spec (.of A)).affineOpens, DividedPowers (I.ideal V))
variable (hc : ∀ (V : (Spec (.of A)).affineOpens) (a : Γ(Spec (.of A), V)),
  (γS V).IsDPMorphism (γS ((Spec (.of A)).affineBasicOpen a))
    ((Spec (.of A)).presheaf.map (homOfLE ((Spec (.of A)).basicOpen_le a)).op).hom)
variable (hI : specIdealEqOfIdealTop IA I) (hγ : specDividedPowersEq IA γA I γS)
variable (hpI : IsNilpotent (Ideal.Quotient.mk IA (p : A)))
variable (F : CrisModuleSheaf (Spec (.of A)) I γS hc (smoothLift f I) (smoothLift_x₀ f I))
variable [hcoherent : SectionsCoherent I γS hc (smoothLift_x₀ f I) F]
variable [hcrystal : CrisModuleSheaf.IsCrystal F]
variable [hqc : CrisModuleSheaf.IsLocallyQuasiCoherent F]
section StageIndex

variable (e : ℕ)

/-- The actual chart map from the descended PD base of this stage. -/
noncomputable def stageAffineSectionMap (V : (stageLift γA hpI f e).affineOpens) :
    stageRing γA hpI e →+* Γ(stageLift γA hpI f e, V) :=
  affineSectionMap (stageToSpec γA hpI f e) V

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
  dividedPowers_ofIdealEq
    (stageAffineSectionMap_map_eq_ker_ideal γA f I hI hpI e V)
    (extensionAlong (stageRing γA hpI e).dividedPowers
      (stageAffineSectionMap γA f hpI e V)
      (stageAffineSectionMap_extendsAlong γA f hpI e V)).dividedPowers

/-- The affine stage structure map is the quotient followed by its smooth chart map. -/
theorem stageAffineSectionMap_comp_quotient (V : (stageLift γA hpI f e).affineOpens) :
    (stageAffineSectionMap γA f hpI e V).comp (quotient γA hpI e).toRingHom =
      affineSectionMap (stageToY γA hpI f e ≫ f) V := sorry

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


/-- The Remark 60.24.11 coefficient module on `Y_e`, obtained by evaluating the
crystal at the actual `p`-power-stage thickening. -/
noncomputable def stageCoefficient : (stageLift γA hpI f e).Modules :=
  F.obj (stageSmallObject γA f I γS hc hI hγ hpI e)

include hqc in
/-- Finite type of the crystal implies coherence of each stage coefficient. -/
instance stageCoefficient_isCoherent [IsNoetherianRing A]
    [hft : ∀ Aobj, (F.obj Aobj).IsFiniteType] :
    (stageCoefficient γA f I γS hc hI hγ hpI F e).IsCoherent :=
  sorry

variable (U : (stageLift γA hpI f e).affineOpens)

/-- The algebra on stage affine-chart functions is induced by `Y_e ⟶ Spec A`. -/
noncomputable abbrev stageChartAlgebra : Algebra A Γ(stageLift γA hpI f e, U.1) :=
  (affineSectionMap (stageToY γA hpI f e ≫ f) U).toAlgebra

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
      Spec.map (CommRingCat.ofHom (affineSectionMap (stageToY γA hpI f e ≫ f) U)) =
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
    (Spec.map (CommRingCat.ofHom (affineSectionMap (stageToY γA hpI f e ≫ f) U)))
    (stageFibre γA f I hI hpI e U) (stageSquare γA f I hI hpI e U)

include hγ in
/-- The affine stage chart agrees with the specified base divided-power structure. -/
theorem stageAffineObject_baseCompatible :
    CrystallineBaseCompatible I γS hc (smoothLift_x₀ f I)
      (stageAffineObject γA f I γS hc hI hpI e U) :=
  sorry


/-- The affine PD connection on a chart of `Y_e`, induced by the crystal and the
square-zero PD thickening of that chart. -/
noncomputable def stageAffineConnection :=
  -- Local instance justification (noncanonical choice): the stage structure map fixes this chart's A-algebra action.
  letI : Algebra A Γ(stageLift γA hpI f e, U.1) := stageChartAlgebra γA f hpI e U
  CrystallinePDSquareZeroGeometry.connection A Γ(stageLift γA hpI f e, U.1)
    (stageDividedPowers γA f I hI hpI e U) I γS hc (smoothLift_x₀ f I)
    (Spec.map (CommRingCat.ofHom (affineSectionMap (stageToY γA hpI f e ≫ f) U)))
    (stageFibre γA f I hI hpI e U) (stageSquare γA f I hI hpI e U)
    (stageIdeal_nil γA f I hI hpI e U)
    (stageAffineObject_baseCompatible γA f I γS hc hI hγ hpI e U)
    (stageFibre_open γA f I hI hpI e U)
    (CrystallinePDSquareZeroGeometry.differentialLift_overAffineBase A
      Γ(stageLift γA hpI f e, U.1) (stageDividedPowers γA f I hI hpI e U)) F

/-- The affine PD de Rham complex of a stage chart. -/
noncomputable def stageComplex :=
  -- Local instance justification (noncanonical choice): the stage structure map fixes this chart's A-algebra action.
  letI : Algebra A Γ(stageLift γA hpI f e, U.1) := stageChartAlgebra γA f hpI e U
  CrystallinePDSquareZeroGeometry.deRhamComplex A Γ(stageLift γA hpI f e, U.1)
    (stageDividedPowers γA f I hI hpI e U) I γS hc (smoothLift_x₀ f I)
    (Spec.map (CommRingCat.ofHom (affineSectionMap (stageToY γA hpI f e ≫ f) U)))
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

/-- The actual affine representative maps to the whole stage object. -/
noncomputable def stageAffineToWhole :
    stageAffineSmallObject γA f I γS hc hI hγ hpI e U ⟶
      stageSmallObject γA f I γS hc hI hγ hpI e :=
  ObjectProperty.homMk
    { source := Over.homMk (stageFibre γA f I hI hpI e U) sorry
      thickening := stageChart γA f hpI e U
      source_comm := sorry
      base_comm := sorry
      ideal_compatible := sorry
      dividedPowers_compatible := sorry }

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
  CrystallineAffineSections.pullbackSectionsIso U
      (stageCoefficient γA f I γS hc hI hγ hpI F e) ≪≫
    ((Scheme.Modules.toPresheaf _).mapIso
      (stageCoefficientIso γA f I γS hc hI hγ hpI F e U)).app (op ⊤)

/-- The genuine affine crystal coefficient of a stage chart. -/
noncomputable def stageCoefficientModule : ModuleCat.{u} Γ(stageLift γA hpI f e, U.1) :=
  (ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of Γ(stageLift γA hpI f e, U.1))).inv.hom).obj
    ((F.obj (stageAffineSmallObject γA f I γS hc hI hγ hpI e U)).val.obj (op ⊤))

/-- The canonical coefficient comparison as a linear equivalence. -/
noncomputable def stageCoefficientSectionsEquiv :
    Γ(stageCoefficient γA f I γS hc hI hγ hpI F e, U.1) ≃ₗ[Γ(stageLift γA hpI f e, U.1)]
      stageCoefficientModule γA f I γS hc hI hγ hpI F e U where
  __ := (stageCoefficientSectionsIso γA f I γS hc hI hγ hpI F e U).addCommGroupIsoToAddEquiv
  map_smul' := sorry

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
  (CrystallineAffineDifferentials.comparison (stageToY γA hpI f e ≫ f) U).comp
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
  (CrystallineAffineTensorSections.tensorMap U
    (stageCoefficient γA f I γS hc hI hγ hpI F e)
    (forms (stageToY γA hpI f e ≫ f) n)).comp
      (TensorProduct.map
        (stageCoefficientSectionsEquiv γA f I γS hc hI hγ hpI F e U).symm.toLinearMap
        ((CrystallineAffineTensorSections.exteriorMap U
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
      map_smul' := sorry }

/-- Affine components of the stage sheaf differential. -/
noncomputable def stageBasisDifferential (n : ℕ) :
    (CrystallineAffineSheafExtension.affineInclusion (stageLift γA hpI f e)).op ⋙
        (stageSheafTerm γA f I γS hc hI hγ hpI F e n).obj ⟶
      (CrystallineAffineSheafExtension.affineInclusion (stageLift γA hpI f e)).op ⋙
        (stageSheafTerm γA f I γS hc hI hγ hpI F e (n + 1)).obj where
  app V := stageLocalLinearDifferential γA f I γS hc hI hγ hpI F e V.unop n
  naturality := sorry

/-- The actual sheaf-level A-linear differential of the stage coefficient. -/
noncomputable def stageSheafDifferential (n : ℕ) :
    stageSheafTerm γA f I γS hc hI hγ hpI F e n ⟶
      stageSheafTerm γA f I γS hc hI hγ hpI F e (n + 1) :=
  CrystallineAffineSheafExtension.extend (stageLift γA hpI f e) _ _
    (stageBasisDifferential γA f I γS hc hI hγ hpI F e n)

/-- The Remark 60.24.11 connection on the stage coefficient, obtained by uniquely
extending the affine PD connections of the crystal. -/
noncomputable def stageConnection :
    asBaseSheaf (stageToY γA hpI f e ≫ f)
      (stageCoefficient γA f I γS hc hI hγ hpI F e) ⟶
      asBaseSheaf (stageToY γA hpI f e ≫ f)
        (oneFormTensor (stageToY γA hpI f e ≫ f)
          (stageCoefficient γA f I γS hc hI hγ hpI F e)) :=
  (CrystallineSheafDegreeBridges.baseDegreeZero (stageToY γA hpI f e ≫ f)
      (stageCoefficient γA f I γS hc hI hγ hpI F e)).inv ≫
    stageSheafDifferential γA f I γS hc hI hγ hpI F e 0 ≫
      (CrystallineSheafDegreeBridges.baseDegreeOne (stageToY γA hpI f e ≫ f)
        (stageCoefficient γA f I γS hc hI hγ hpI F e)).hom

/-- The Remark 60.24.11 stage connection satisfies the sheaf Leibniz law. -/
instance stageConnection_isConnection :
    IsConnection (stageToY γA hpI f e ≫ f)
      (stageCoefficient γA f I γS hc hI hγ hpI F e)
      (stageConnection γA f I γS hc hI hγ hpI F e) :=
  sorry

/-- The PD connection of a stage chart is integrable. -/
theorem stageConnection_integrable :
    stageConnection γA f I γS hc hI hγ hpI F e ≫
      (CrystallineSheafDegreeBridges.baseDegreeOne (stageToY γA hpI f e ≫ f)
        (stageCoefficient γA f I γS hc hI hγ hpI F e)).inv ≫
      stageSheafDifferential γA f I γS hc hI hγ hpI F e 1 = 0 :=
  sorry

/-- The actual crystalline transition fixes the original closed fibre and
uses the spectrum of the stable quotient transition on the thickenings. -/
noncomputable def stageObjectStep :
    CrystallineObject.Hom (stageObject γA f I γS hc hI hpI e)
      (stageObject γA f I γS hc hI hpI (e + 1)) where
  source := 𝟙 _
  thickening := stageStep γA hpI f e
  source_comm := sorry
  base_comm := sorry
  ideal_compatible := sorry
  dividedPowers_compatible := sorry

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
    (Scheme.Modules.pullbackCongr (stageStepToY γA hpI f e)).app FY

/-- The reduction step is the canonical pullback-composition identification. -/
theorem reductionStep_hom (FY : Y.Modules) (e : ℕ) :
    (reductionStep γA f hpI FY e).hom =
      ((Scheme.Modules.pullbackComp (stageStep γA hpI f e)
          (stageToY γA hpI f (e + 1))).app FY ≪≫
        (Scheme.Modules.pullbackCongr (stageStepToY γA hpI f e)).app FY).hom :=
  sorry

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

end CrystallineCompleteStages
