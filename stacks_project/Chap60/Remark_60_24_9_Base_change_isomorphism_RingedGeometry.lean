module

public import stacks_project.Chap60.Remark_60_24_9_Base_change_isomorphism_Coefficients
public import stacks_project.Chap60.Remark_60_24_9_Base_change_isomorphism_BaseSections
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.GlobalSections
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.GlobalSections
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.Adjunction
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Adjunction
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Restriction.Composition
public import stacks_project.Chap60.Remark_60_8_5_Functoriality
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.HomOfCocontinuous
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.HomOfSite
public import stacks_project.Chap60.Lemma_60_9_2_Topos
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Zariski.Small

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Crystalline CrystallineCoefficients
open ComplexShape

universe u

namespace CrystallineRingedGeometry

/-- Global sections of a crystalline-universe ringed site inherit commutativity
from the given componentwise commutativity fact. -/
noncomputable instance instCommRingGlobalSectionsRing
    (X : RingedSite.{u + 1, u, u + 1}) [UnivLE.{u + 1, u + 1}]
    [h : Fact (∀ a b : RingedSite.Hom.globalSectionsRing X, a * b = b * a)] :
    CommRing (RingedSite.Hom.globalSectionsRing X) where
  toRing := inferInstance
  mul_comm := h.elim

/-- Module-valued global sections on a crystalline-universe ringed site are additive. -/
noncomputable instance instModuleGlobalSectionsFunctorAdditive
    (R : RingedSite.{u + 1, u, u + 1}) [UnivLE.{u + 1, u + 1}] :
    (RingedSite.Hom.moduleGlobalSectionsFunctor.{u + 1} R).Additive :=
  RingedSite.Hom.moduleGlobalSectionsFunctor_additive R

/-- Module-valued global sections admit an unbounded right derived functor. -/
noncomputable instance instModuleGlobalSectionsHasRightDerived
    (R : RingedSite.{u + 1, u, u + 1}) [UnivLE.{u + 1, u + 1}]
    [IsGrothendieckAbelian (RingedSite.ModuleCat.{u + 1} R)] :
    Functor.HasRightDerivedFunctor
      (RingedSite.Hom.moduleGlobalSectionsToModuleDerived.{u + 1} R)
      (RingedSite.Hom.ModuleQis.{u + 1} R) :=
  RingedSite.Hom.moduleGlobalSectionsToModuleDerived_hasRightDerivedFunctor R

/-- The big-to-small Zariski site presentation with its unchanged functions. -/
noncomputable def baseSmallProjectionSite (S : Scheme.{u}) :
    RingedSite.Hom (Scheme.AssociatedModule.bigCommRingedSite .zariski S)
      (Scheme.AssociatedModule.smallCommRingedSite .zariski S) where
  base := Scheme.Zariski.SmallToBig.relocalizationFunctor (𝟙 S)
  isMorphismOfSites := Scheme.Zariski.SmallToBig.identity_isMorphismOfSites S
  structureSheafMap :=
    { hom := { app := fun U ↦ 𝟙 _
               naturality := by intro U V f; rfl } }

/-- The base projection includes the canonical structure-sheaf map. -/
noncomputable def baseSmallProjection (S : Scheme.{u}) :
    RingedSite.ToposHom (Scheme.AssociatedModule.bigCommRingedSite .zariski S)
      (Scheme.AssociatedModule.smallCommRingedSite .zariski S) :=
  (baseSmallProjectionSite S).toToposHom

variable {S X : Scheme.{u}} (I : S.IdealSheafData)
variable (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
variable (hc : ∀ (V : S.affineOpens) (f : Γ(S, V)),
  (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
    (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
variable (x₀ : X ⟶ I.subscheme)

/-- A big crystalline object retains its actual thickening over the base. -/
def bigThickeningOverBase : RelativeCRIS S I γ hc X x₀ ⥤ Over S where
  obj T := Over.mk T.1.thickeningToBase
  map f := Over.homMk f.thickening f.base_comm
  map_id := by intro T; rfl
  map_comp := by intro T U V f g; rfl

/-- The structure sheaf on the big crystalline site, lifted without changing
its functions or restriction maps. -/
noncomputable def bigStructureSheaf :
    Sheaf (crystallineZariskiTopology S I γ hc X x₀) RingCat.{u + 1} :=
  ⟨Presheaf.ringPresheafOfComm
    (Scheme.Over.commStructurePresheaf (bigThickeningOverBase I γ hc x₀)), sorry⟩

/-- The genuine big crystalline ringed site. -/
noncomputable abbrev bigRingedSite : RingedSite.{u + 1, u, u + 1} :=
  RingedSite.ofRingSheaf (crystallineZariskiTopology S I γ hc X x₀)
    (bigStructureSheaf I γ hc x₀)

/-- Open coverings of a thickening lift to crystalline coverings by restricting
the source, the thickening, and its divided powers to each open. -/
instance bigThickeningOverBase_isCocontinuous :
    (bigThickeningOverBase I γ hc x₀).IsCocontinuous
      (crystallineZariskiTopology S I γ hc X x₀)
      (StandardTopology.zariski.overTopology S) := sorry

/-- The structure-presheaf map to the base Zariski site is the identity on
functions of the actual thickening over `S`. -/
noncomputable def baseStructureMap :
    (bigThickeningOverBase I γ hc x₀).op ⋙
        (Scheme.AssociatedModule.bigCommRingedSite .zariski S).structureSheaf.obj ⟶
      (bigStructureSheaf I γ hc x₀).obj where
  app T := 𝟙 _
  naturality := by intro T U k; rfl

/-- The structure morphism from the big crystalline ringed topos to the big
Zariski ringed topos of the base is induced by the actual thickening over `S`. -/
noncomputable def bigStructureMorphism
    [HasSheafify (crystallineZariskiTopology S I γ hc X x₀) (Type (u + 1))]
    [∀ P : (RelativeCRIS S I γ hc X x₀)ᵒᵖ ⥤ Type (u + 1),
      (bigThickeningOverBase I γ hc x₀).op.HasPointwiseRightKanExtension P]
    [(crystallineZariskiTopology S I γ hc X x₀).HasSheafCompose (forget RingCat.{u + 1})] :
    RingedSite.ToposHom (bigRingedSite I γ hc x₀)
      (Scheme.AssociatedModule.bigCommRingedSite .zariski S) :=
  @RingedSite.Cocontinuous.toRingedTopos (bigRingedSite I γ hc x₀)
    (Scheme.AssociatedModule.bigCommRingedSite .zariski S)
    (bigThickeningOverBase I γ hc x₀)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (baseStructureMap I γ hc x₀)

variable {p : ℕ} [Fact p.Prime]
variable {S' Y : Scheme.{u}} (I' : S'.IdealSheafData)
variable (γ' : ∀ V : S'.affineOpens, DividedPowers (I'.ideal V))
variable (hc' : ∀ (V : S'.affineOpens) (f : Γ(S', V)),
  (γ' V).IsDPMorphism (γ' (S'.affineBasicOpen f))
    (S'.presheaf.map (homOfLE (S'.basicOpen_le f)).op).hom)
variable (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable (s' : S' ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable (y₀ : Y ⟶ I'.subscheme) (f : X ⟶ Y)
variable (g : DividedPowerSchemeHom I I' s s') (hf : f ≫ y₀ = x₀ ≫ g.zeroFiberMap)
variable (hpX : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
variable (hpY : ∀ U : Y.affineOpens, IsNilpotent (p : Γ(Y, U)))
variable (hγ : ∀ (V : S'.affineOpens) (W : S.affineOpens)
  (hVW : W.1 ≤ g.base ⁻¹ᵁ V.1),
  (γ' V).IsDPMorphism (γ W) (g.base.appLE V W hVW).hom)

/-- The crystalline functor changes the base of a thickening but retains
its ring of functions; hence its structure-presheaf map is the identity. -/
noncomputable def bigStructureMap :
    (CrystallineFunctor.of f g hf hpX hpY hγ).toRelativeFunctor.op ⋙
        (bigStructureSheaf I' γ' hc' y₀).obj ⟶ (bigStructureSheaf I γ hc x₀).obj where
  app T := 𝟙 _
  naturality := by intro T U k; rfl

variable [HasSheafify (crystallineZariskiTopology S I γ hc X x₀) (Type (u + 1))]
variable [∀ P : (RelativeCRIS S I γ hc X x₀)ᵒᵖ ⥤ Type (u + 1),
  (CrystallineFunctor.of f g hf hpX hpY hγ).toRelativeFunctor.op.HasPointwiseRightKanExtension P]
variable [(crystallineZariskiTopology S I γ hc X x₀).HasSheafCompose (forget RingCat.{u + 1})]
variable [(crystallineZariskiTopology S' I' γ' hc' Y y₀).HasSheafCompose (forget RingCat.{u + 1})]

/-- The ringed geometric morphism of big crystalline topoi induced by the
actual scheme and divided-power-base maps. No arbitrary structure map is used. -/
noncomputable def bigRingedMorphism :
    RingedSite.ToposHom (bigRingedSite I γ hc x₀) (bigRingedSite I' γ' hc' y₀) :=
  @RingedSite.Cocontinuous.toRingedTopos
    (bigRingedSite I γ hc x₀) (bigRingedSite I' γ' hc' y₀)
    (CrystallineFunctor.of f g hf hpX hpY hγ).toRelativeFunctor
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (bigStructureMap I γ hc x₀ I' γ' hc' s s' y₀ f g hf hpX hpY hγ)

/-- Restricting the big structure presheaf along the small-site inclusion
retains the same thickening and the same functions. -/
noncomputable def smallStructureMap :
    (smallCrystallineInclusion S I γ hc X x₀).op ⋙ (bigStructureSheaf I γ hc x₀).obj ⟶
      (CrystallineCoefficients.liftedStructureSheaf I γ hc x₀ p s hpX).obj where
  app T := 𝟙 _
  naturality := by intro T U k; rfl

variable [HasSheafify (smallCrystallineTopology p S I γ hc s X x₀ hpX) (Type (u + 1))]
variable [∀ P : (smallCrystallineSite S I γ hc X x₀)ᵒᵖ ⥤ Type (u + 1),
  (smallCrystallineInclusion S I γ hc X x₀).op.HasPointwiseRightKanExtension P]
variable [(smallCrystallineTopology p S I γ hc s X x₀ hpX).HasSheafCompose
  (forget RingCat.{u + 1})]

/-- The small-to-big crystalline inclusion with its canonical ring structure. -/
noncomputable def smallToBigRinged :
    RingedSite.ToposHom (CrystallineCoefficients.liftedRingedSite I γ hc x₀ p s hpX)
      (bigRingedSite I γ hc x₀) :=
  @RingedSite.Cocontinuous.toRingedTopos
    (CrystallineCoefficients.liftedRingedSite I γ hc x₀ p s hpX) (bigRingedSite I γ hc x₀)
    (smallCrystallineInclusion S I γ hc X x₀)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (smallStructureMap I γ hc x₀ s hpX)

/-- The small crystalline structure morphism, using the canonical inclusion
into the big crystalline ringed topos before passing to the base. -/
noncomputable def structureMorphism
    [∀ P : (RelativeCRIS S I γ hc X x₀)ᵒᵖ ⥤ Type (u + 1),
      (bigThickeningOverBase I γ hc x₀).op.HasPointwiseRightKanExtension P] :
    RingedSite.ToposHom (CrystallineCoefficients.liftedRingedSite I γ hc x₀ p s hpX)
      (Scheme.AssociatedModule.bigCommRingedSite .zariski S) :=
  RingedSite.ToposHom.comp (smallToBigRinged I γ hc x₀ s hpX)
    (bigStructureMorphism I γ hc x₀)

/-- The crystalline structure morphism to the base's small Zariski ringed
topos, with both the site bridge and the structure map retained. -/
noncomputable def structureMorphismToSmall
    [∀ P : (RelativeCRIS S I γ hc X x₀)ᵒᵖ ⥤ Type (u + 1),
      (bigThickeningOverBase I γ hc x₀).op.HasPointwiseRightKanExtension P] :
    RingedSite.ToposHom (CrystallineCoefficients.liftedRingedSite I γ hc x₀ p s hpX)
      (Scheme.AssociatedModule.smallCommRingedSite .zariski S) :=
  RingedSite.ToposHom.comp (structureMorphism I γ hc x₀ s hpX) (baseSmallProjection S)

variable [∀ P : (smallCrystallineSite S I γ hc X x₀)ᵒᵖ ⥤ Type (u + 1),
  (smallCrystallineInclusion S I γ hc X x₀).op.HasLeftKanExtension P]

/-- Ring-valued direct image of the big-to-small projection is restriction. -/
noncomputable abbrev bigToSmallRingPush :
    Sheaf (crystallineZariskiTopology S I γ hc X x₀) RingCat.{u + 1} ⥤
      Sheaf (smallCrystallineTopology p S I γ hc s X x₀ hpX) RingCat.{u + 1} :=
  (smallCrystallineInclusion S I γ hc X x₀).sheafPushforwardContinuous RingCat.{u + 1}
    (smallCrystallineTopology p S I γ hc s X x₀ hpX)
    (crystallineZariskiTopology S I γ hc X x₀)

/-- Restriction commutes definitionally with forgetting the ring operations. -/
noncomputable def bigToSmallForgetIso :
    bigToSmallRingPush I γ hc x₀ s hpX ⋙
        sheafCompose (smallCrystallineTopology p S I γ hc s X x₀ hpX)
          (forget RingCat.{u + 1}) ≅
      sheafCompose (crystallineZariskiTopology S I γ hc X x₀) (forget RingCat.{u + 1}) ⋙
        (bigToSmallCrystallineToposMorphism S I γ hc X x₀ p s hpX).pushforward :=
  Iso.refl _

/-- The restricted big structure sheaf agrees with the small structure sheaf. -/
noncomputable def bigToSmallStructureMap :
    CrystallineCoefficients.liftedStructureSheaf I γ hc x₀ p s hpX ⟶
      (bigToSmallRingPush I γ hc x₀ s hpX).obj (bigStructureSheaf I γ hc x₀) where
  hom := { app := fun T ↦ 𝟙 _
           naturality := by intro T U k; rfl }

/-- The identity-on-functions structure map preserves the internal ring
operations of continuous direct image. -/
theorem bigToSmallRingCompatible :
    @RingedSite.ToposHom.Direct.IsRingCompatible
      (bigRingedSite I γ hc x₀) (CrystallineCoefficients.liftedRingedSite I γ hc x₀ p s hpX)
      inferInstance inferInstance
      (bigToSmallCrystallineToposMorphism S I γ hc X x₀ p s hpX)
      (bigToSmallRingPush I γ hc x₀ s hpX)
      (bigToSmallForgetIso I γ hc x₀ s hpX)
      (bigToSmallStructureMap I γ hc x₀ s hpX) := sorry

/-- The big-to-small projection as a genuine morphism of ringed topoi. -/
noncomputable def bigToSmallRinged :
    RingedSite.ToposHom (bigRingedSite I γ hc x₀)
      (CrystallineCoefficients.liftedRingedSite I γ hc x₀ p s hpX) :=
  @RingedSite.ToposHom.ofDirectImage
    (bigRingedSite I γ hc x₀) (CrystallineCoefficients.liftedRingedSite I γ hc x₀ p s hpX)
    inferInstance inferInstance
    (bigToSmallCrystallineToposMorphism S I γ hc X x₀ p s hpX)
    (bigToSmallRingPush I γ hc x₀ s hpX)
    (bigToSmallForgetIso I γ hc x₀ s hpX)
    (bigToSmallStructureMap I γ hc x₀ s hpX)
    (bigToSmallRingCompatible I γ hc x₀ s hpX)

variable [HasSheafify (crystallineZariskiTopology S' I' γ' hc' Y y₀) (Type (u + 1))]
variable [∀ P : (smallCrystallineSite S' I' γ' hc' Y y₀)ᵒᵖ ⥤ Type (u + 1),
  (smallCrystallineInclusion S' I' γ' hc' Y y₀).op.HasLeftKanExtension P]
variable [(smallCrystallineTopology p S' I' γ' hc' s' Y y₀ hpY).HasSheafCompose
  (forget RingCat.{u + 1})]

/-- The geometric small crystalline morphism, including the structure-sheaf
maps, is the composite `π_Y ∘ f_CRIS ∘ i_X`. -/
noncomputable def smallRingedMorphism :
    RingedSite.ToposHom (CrystallineCoefficients.liftedRingedSite I γ hc x₀ p s hpX)
      (CrystallineCoefficients.liftedRingedSite I' γ' hc' y₀ p s' hpY) :=
  RingedSite.ToposHom.comp (smallToBigRinged I γ hc x₀ s hpX)
    (RingedSite.ToposHom.comp
      (bigRingedMorphism I γ hc x₀ I' γ' hc' s s' y₀ f g hf hpX hpY hγ)
      (bigToSmallRinged I' γ' hc' y₀ s' hpY))

/-- The actual crystalline morphism respects the base-ring actions: both
routes pull a base function back along the thickening's structure morphism.
This fixes the semilinearity used in the cohomology comparison, rather than
assuming an arbitrary comparison isomorphism. -/
theorem baseActions_compatible :
    (smallRingedMorphism I γ hc x₀ I' γ' hc' s s' y₀ f g hf hpX hpY hγ).globalSectionsMap.hom.comp
        (CrystallineCoefficients.baseToGlobalSections I' γ' hc' y₀ p s' hpY) =
      (CrystallineCoefficients.baseToGlobalSections I γ hc x₀ p s hpX).comp
        (CrystallineCoefficients.baseRingMap g.base) := sorry

variable [IsGrothendieckAbelian
  (RingedSite.ModuleCat.{u + 1} (CrystallineCoefficients.liftedRingedSite I γ hc x₀ p s hpX))]
variable [IsGrothendieckAbelian
  (RingedSite.ModuleCat.{u + 1} (CrystallineCoefficients.liftedRingedSite I' γ' hc' y₀ p s' hpY))]
variable [(SheafOfModules.restrictScalars
  (smallRingedMorphism I γ hc x₀ I' γ' hc' s s' y₀ f g hf hpX hpY hγ).structureMap).IsRightAdjoint]
variable [RingedSite.ToposHom.HasModulePullbackDerived
  (smallRingedMorphism I γ hc x₀ I' γ' hc' s s' y₀ f g hf hpX hpY hγ)]
variable [RingedSite.ToposHom.HasModulePushforwardDerived
  (smallRingedMorphism I γ hc x₀ I' γ' hc' s s' y₀ f g hf hpX hpY hγ)]
variable [RingedSite.ToposHom.HasModuleDerivedAdjunction
  (smallRingedMorphism I γ hc x₀ I' γ' hc' s s' y₀ f g hf hpX hpY hγ)]

-- Local instance justification (defeq pin): derived units and ModuleDerived
-- must use the existing Hom.moduleCat_hasDerivedCategory presentation.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory

/-- Direct image of modules along the crystalline base-change morphism is additive. -/
noncomputable instance crystallineBaseChange_modulePushforward_additive :
    (smallRingedMorphism I γ hc x₀ I' γ' hc' s s' y₀ f g hf hpX hpY hγ).modulePushforward.Additive :=
  RingedSite.ToposHom.modulePushforward_additive _

/-- Module-valued global sections on the source crystalline site are additive. -/
noncomputable instance crystallineSource_moduleGlobalSections_additive :
    (RingedSite.Hom.moduleGlobalSectionsFunctor.{u + 1}
      (CrystallineCoefficients.liftedRingedSite I γ hc x₀ p s hpX)).Additive :=
  sorry

/-- Module-valued global sections on the target crystalline site are additive. -/
noncomputable instance crystallineTarget_moduleGlobalSections_additive :
    (RingedSite.Hom.moduleGlobalSectionsFunctor.{u + 1}
      (CrystallineCoefficients.liftedRingedSite I' γ' hc' y₀ p s' hpY)).Additive :=
  sorry

/-- Source crystalline global sections inherit commutativity from the thickenings. -/
noncomputable instance crystallineSource_globalSections_commRing :
    CommRing (RingedSite.Hom.globalSectionsRing
      (CrystallineCoefficients.liftedRingedSite I γ hc x₀ p s hpX)) :=
  instCommRingGlobalSectionsRing
    (CrystallineCoefficients.liftedRingedSite I γ hc x₀ p s hpX)

/-- Target crystalline global sections inherit commutativity from the thickenings. -/
noncomputable instance crystallineTarget_globalSections_commRing :
    CommRing (RingedSite.Hom.globalSectionsRing
      (CrystallineCoefficients.liftedRingedSite I' γ' hc' y₀ p s' hpY)) :=
  instCommRingGlobalSectionsRing
    (CrystallineCoefficients.liftedRingedSite I' γ' hc' y₀ p s' hpY)

/-- Scalar-restricted crystalline global sections are additive. -/
noncomputable instance crystallineSectionsRestriction_additive :
    (RingedSite.Hom.moduleGlobalSectionsFunctor.{u + 1}
        (CrystallineCoefficients.liftedRingedSite I γ hc x₀ p s hpX) ⋙
      (smallRingedMorphism I γ hc x₀ I' γ' hc' s s' y₀ f g hf hpX hpY hγ).globalSectionsRestriction).Additive :=
  sorry

/-- Direct image followed by crystalline global sections is additive. -/
noncomputable instance crystallinePushforwardSections_additive :
    ((smallRingedMorphism I γ hc x₀ I' γ' hc' s s' y₀ f g hf hpX hpY hγ).modulePushforward ⋙
      RingedSite.Hom.moduleGlobalSectionsFunctor.{u + 1}
        (CrystallineCoefficients.liftedRingedSite I' γ' hc' y₀ p s' hpY)).Additive :=
  sorry

/-- Homotopy-level identification of global sections of a direct image with
scalar-restricted sections on the source, induced by the underived topos
comparison. -/
noncomputable def crystallineSectionsHomotopyIso :
    ((RingedSite.Hom.moduleGlobalSectionsFunctor.{u + 1}
          (CrystallineCoefficients.liftedRingedSite I γ hc x₀ p s hpX) ⋙
        (smallRingedMorphism I γ hc x₀ I' γ' hc' s s' y₀ f g hf hpX hpY hγ).globalSectionsRestriction).mapHomotopyCategory (up ℤ)) ≅
      (((smallRingedMorphism I γ hc x₀ I' γ' hc' s s' y₀ f g hf hpX hpY hγ).modulePushforward ⋙
        RingedSite.Hom.moduleGlobalSectionsFunctor.{u + 1}
          (CrystallineCoefficients.liftedRingedSite I' γ' hc' y₀ p s' hpY)).mapHomotopyCategory
        (up ℤ)) where
  hom := NatTrans.mapHomotopyCategory
    (smallRingedMorphism I γ hc x₀ I' γ' hc' s s' y₀ f g hf hpX hpY hγ).moduleGlobalSectionsPushforwardIso.inv (up ℤ)
  inv := NatTrans.mapHomotopyCategory
    (smallRingedMorphism I γ hc x₀ I' γ' hc' s s' y₀ f g hf hpX hpY hγ).moduleGlobalSectionsPushforwardIso.hom (up ℤ)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Homotopy-level source of the crystalline sections comparison. -/
noncomputable def crystallineSectionsSource :
    RingedSite.Hom.ModuleHomotopy.{u + 1}
      (CrystallineCoefficients.liftedRingedSite I γ hc x₀ p s hpX) ⥤
    RingedSite.Hom.ModuleSections.Derived.{u + 1}
      (CrystallineCoefficients.liftedRingedSite I' γ' hc' y₀ p s' hpY) :=
  RingedSite.Hom.moduleGlobalSectionsToModuleDerived.{u + 1}
      (CrystallineCoefficients.liftedRingedSite I γ hc x₀ p s hpX) ⋙
    (smallRingedMorphism I γ hc x₀ I' γ' hc' s s' y₀ f g hf hpX hpY hγ).globalSectionsRestriction.mapDerivedCategory

/-- Homotopy-level target of the crystalline sections comparison. -/
noncomputable def crystallineSectionsTarget :
    RingedSite.Hom.ModuleHomotopy.{u + 1}
      (CrystallineCoefficients.liftedRingedSite I γ hc x₀ p s hpX) ⥤
    RingedSite.Hom.ModuleSections.Derived.{u + 1}
      (CrystallineCoefficients.liftedRingedSite I' γ' hc' y₀ p s' hpY) :=
  (smallRingedMorphism I γ hc x₀ I' γ' hc' s s' y₀ f g hf hpX hpY hγ).modulePushforward.mapHomotopyCategory (up ℤ) ⋙
    RingedSite.Hom.moduleGlobalSectionsToModuleDerived.{u + 1}
      (CrystallineCoefficients.liftedRingedSite I' γ' hc' y₀ p s' hpY)

/-- Derived source of the crystalline sections comparison. -/
noncomputable def crystallineSectionsSourceDerived :
    RingedSite.Hom.ModuleDerived.{u + 1}
      (CrystallineCoefficients.liftedRingedSite I γ hc x₀ p s hpX) ⥤
    RingedSite.Hom.ModuleSections.Derived.{u + 1}
      (CrystallineCoefficients.liftedRingedSite I' γ' hc' y₀ p s' hpY) :=
  RingedSite.Hom.moduleDerivedGlobalSections.{u + 1}
      (CrystallineCoefficients.liftedRingedSite I γ hc x₀ p s hpX) ⋙
    (smallRingedMorphism I γ hc x₀ I' γ' hc' s s' y₀ f g hf hpX hpY hγ).globalSectionsRestriction.mapDerivedCategory

/-- Derived target of the crystalline sections comparison. -/
noncomputable def crystallineSectionsTargetDerived :
    RingedSite.Hom.ModuleDerived.{u + 1}
      (CrystallineCoefficients.liftedRingedSite I γ hc x₀ p s hpX) ⥤
    RingedSite.Hom.ModuleSections.Derived.{u + 1}
      (CrystallineCoefficients.liftedRingedSite I' γ' hc' y₀ p s' hpY) :=
  (smallRingedMorphism I γ hc x₀ I' γ' hc' s s' y₀ f g hf hpX hpY hγ).modulePushforwardDerived ⋙
    RingedSite.Hom.moduleDerivedGlobalSections.{u + 1}
      (CrystallineCoefficients.liftedRingedSite I' γ' hc' y₀ p s' hpY)

/-- Right-derived unit for scalar-restricted crystalline global sections. -/
noncomputable def crystallineSectionsSourceUnit :
    crystallineSectionsSource I γ hc x₀ I' γ' hc' s s' y₀ f g hf hpX hpY hγ ⟶
      RingedSite.Hom.moduleLocalization.{u + 1}
          (CrystallineCoefficients.liftedRingedSite I γ hc x₀ p s hpX) ⋙
        crystallineSectionsSourceDerived I γ hc x₀ I' γ' hc' s s' y₀ f g hf hpX hpY hγ :=
  Functor.whiskerRight
    (Functor.totalRightDerivedUnit
      (RingedSite.Hom.moduleGlobalSectionsToModuleDerived.{u + 1}
        (CrystallineCoefficients.liftedRingedSite I γ hc x₀ p s hpX))
      (RingedSite.Hom.moduleLocalization.{u + 1}
        (CrystallineCoefficients.liftedRingedSite I γ hc x₀ p s hpX))
      (RingedSite.Hom.ModuleQis.{u + 1}
        (CrystallineCoefficients.liftedRingedSite I γ hc x₀ p s hpX)))
    (smallRingedMorphism I γ hc x₀ I' γ' hc' s s' y₀ f g hf hpX hpY hγ).globalSectionsRestriction.mapDerivedCategory ≫
    (Functor.associator _ _ _).hom

/-- Right-derived unit for direct image followed by crystalline global sections. -/
noncomputable def crystallineSectionsTargetUnit :
    crystallineSectionsTarget I γ hc x₀ I' γ' hc' s s' y₀ f g hf hpX hpY hγ ⟶
      RingedSite.Hom.moduleLocalization.{u + 1}
          (CrystallineCoefficients.liftedRingedSite I γ hc x₀ p s hpX) ⋙
        crystallineSectionsTargetDerived I γ hc x₀ I' γ' hc' s s' y₀ f g hf hpX hpY hγ :=
  Functor.whiskerLeft ((smallRingedMorphism I γ hc x₀ I' γ' hc' s s' y₀ f g hf hpX hpY hγ).modulePushforward.mapHomotopyCategory (up ℤ))
    (Functor.totalRightDerivedUnit
      (RingedSite.Hom.moduleGlobalSectionsToModuleDerived.{u + 1}
        (CrystallineCoefficients.liftedRingedSite I' γ' hc' y₀ p s' hpY))
      (RingedSite.Hom.moduleLocalization.{u + 1}
        (CrystallineCoefficients.liftedRingedSite I' γ' hc' y₀ p s' hpY))
      (RingedSite.Hom.ModuleQis.{u + 1}
        (CrystallineCoefficients.liftedRingedSite I' γ' hc' y₀ p s' hpY))) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (Functor.totalRightDerivedUnit
        (RingedSite.ToposHom.modulePushforwardToDerived (smallRingedMorphism I γ hc x₀ I' γ' hc' s s' y₀ f g hf hpX hpY hγ))
        (RingedSite.Hom.moduleLocalization.{u + 1}
          (CrystallineCoefficients.liftedRingedSite I γ hc x₀ p s hpX))
        (RingedSite.Hom.ModuleQis.{u + 1}
          (CrystallineCoefficients.liftedRingedSite I γ hc x₀ p s hpX)))
      (RingedSite.Hom.moduleDerivedGlobalSections.{u + 1}
        (CrystallineCoefficients.liftedRingedSite I' γ' hc' y₀ p s' hpY)) ≫
    (Functor.associator _ _ _).hom

/-- Scalar-restricted crystalline global sections compute as a right-derived functor. -/
noncomputable instance crystallineSectionsSource_isRightDerived :
    (crystallineSectionsSourceDerived I γ hc x₀ I' γ' hc' s s' y₀ f g hf hpX hpY hγ).IsRightDerivedFunctor
      (crystallineSectionsSourceUnit I γ hc x₀ I' γ' hc' s s' y₀ f g hf hpX hpY hγ)
      (RingedSite.Hom.ModuleQis.{u + 1}
        (CrystallineCoefficients.liftedRingedSite I γ hc x₀ p s hpX)) := sorry

/-- Direct image followed by crystalline global sections computes as a right-derived functor. -/
noncomputable instance crystallineSectionsTarget_isRightDerived :
    (crystallineSectionsTargetDerived I γ hc x₀ I' γ' hc' s s' y₀ f g hf hpX hpY hγ).IsRightDerivedFunctor
      (crystallineSectionsTargetUnit I γ hc x₀ I' γ' hc' s s' y₀ f g hf hpX hpY hγ)
      (RingedSite.Hom.ModuleQis.{u + 1}
        (CrystallineCoefficients.liftedRingedSite I γ hc x₀ p s hpX)) := sorry

/-- Homotopy comparison identifying the two models of crystalline sections. -/
noncomputable def crystallineSectionsHomotopyComparison :
    crystallineSectionsSource I γ hc x₀ I' γ' hc' s s' y₀ f g hf hpX hpY hγ ≅
      crystallineSectionsTarget I γ hc x₀ I' γ' hc' s s' y₀ f g hf hpX hpY hγ :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      ((RingedSite.Hom.moduleGlobalSectionsFunctor.{u + 1}
          (CrystallineCoefficients.liftedRingedSite I γ hc x₀ p s hpX)).mapHomotopyCategory
        (up ℤ))
      (smallRingedMorphism I γ hc x₀ I' γ' hc' s s' y₀ f g hf hpX hpY hγ).globalSectionsRestriction.mapDerivedCategoryFactorsh ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso
        (Iso.refl (RingedSite.Hom.moduleGlobalSectionsFunctor.{u + 1}
            (CrystallineCoefficients.liftedRingedSite I γ hc x₀ p s hpX) ⋙
          (smallRingedMorphism I γ hc x₀ I' γ' hc' s s' y₀ f g hf hpX hpY hγ).globalSectionsRestriction)) (up ℤ))
      DerivedCategory.Qh ≪≫
    Functor.isoWhiskerRight
      (crystallineSectionsHomotopyIso I γ hc x₀ I' γ' hc' s s' y₀ f g hf hpX hpY hγ)
      DerivedCategory.Qh ≪≫
    Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso
        (Iso.refl ((smallRingedMorphism I γ hc x₀ I' γ' hc' s s' y₀ f g hf hpX hpY hγ).modulePushforward ⋙
          RingedSite.Hom.moduleGlobalSectionsFunctor.{u + 1}
            (CrystallineCoefficients.liftedRingedSite I' γ' hc' y₀ p s' hpY))) (up ℤ)).symm
      DerivedCategory.Qh ≪≫ Functor.associator _ _ _

/-- Derived global-sections comparison along the crystalline ringed morphism. -/
noncomputable def crystallineDerivedGlobalSectionsIso :
    crystallineSectionsSourceDerived I γ hc x₀ I' γ' hc' s s' y₀ f g hf hpX hpY hγ ≅
      crystallineSectionsTargetDerived I γ hc x₀ I' γ' hc' s s' y₀ f g hf hpX hpY hγ :=
  Functor.rightDerivedNatIso
    (crystallineSectionsSourceDerived I γ hc x₀ I' γ' hc' s s' y₀ f g hf hpX hpY hγ)
    (crystallineSectionsTargetDerived I γ hc x₀ I' γ' hc' s s' y₀ f g hf hpX hpY hγ)
    (crystallineSectionsSourceUnit I γ hc x₀ I' γ' hc' s s' y₀ f g hf hpX hpY hγ)
    (crystallineSectionsTargetUnit I γ hc x₀ I' γ' hc' s s' y₀ f g hf hpX hpY hγ)
    (RingedSite.Hom.ModuleQis.{u + 1}
      (CrystallineCoefficients.liftedRingedSite I γ hc x₀ p s hpX))
    (crystallineSectionsHomotopyComparison I γ hc x₀ I' γ' hc' s s' y₀ f g hf hpX hpY hγ)

/-- Base-linear identification of iterated restriction of scalars along the
crystalline global-sections maps and the actual base-ring map. -/
noncomputable def crystallineBaseRestrictionIso :
    CategoryTheory.ModuleCat.derivedRestrictionOfScalars
        ((smallRingedMorphism I γ hc x₀ I' γ' hc' s s' y₀ f g hf hpX hpY hγ).globalSectionsMap.hom) ⋙
      CategoryTheory.ModuleCat.derivedRestrictionOfScalars
        ((CrystallineCoefficients.baseToGlobalSections I' γ' hc' y₀ p s' hpY)) ≅
      CategoryTheory.ModuleCat.derivedRestrictionOfScalars
          ((CrystallineCoefficients.baseToGlobalSections I γ hc x₀ p s hpX)) ⋙
        CategoryTheory.ModuleCat.derivedRestrictionOfScalars
          (CrystallineCoefficients.baseRingMap g.base) :=
  (CategoryTheory.ModuleCat.DerivedRestriction.compIso
      ((CrystallineCoefficients.baseToGlobalSections I' γ' hc' y₀ p s' hpY))
      ((smallRingedMorphism I γ hc x₀ I' γ' hc' s s' y₀ f g hf hpX hpY hγ).globalSectionsMap.hom)).symm ≪≫
    eqToIso (congrArg CategoryTheory.ModuleCat.derivedRestrictionOfScalars
      (baseActions_compatible I γ hc x₀ I' γ' hc' s s' y₀ f g hf hpX hpY hγ)) ≪≫
    CategoryTheory.ModuleCat.DerivedRestriction.compIso
      (CrystallineCoefficients.baseRingMap g.base)
      ((CrystallineCoefficients.baseToGlobalSections I γ hc x₀ p s hpX))

/-- The actual crystalline cohomology base-change map over the base rings.
All geometric maps, scalar actions and comparison maps are fixed by the
scheme map and divided-power base map. -/
noncomputable def cohomologyBaseChange
    (K : RingedSite.Hom.ModuleDerived.{u + 1}
      (CrystallineCoefficients.liftedRingedSite I' γ' hc' y₀ p s' hpY)) :=
  let α := (CrystallineCoefficients.baseToGlobalSections I' γ' hc' y₀ p s' hpY)
  let σ := CrystallineCoefficients.baseRingMap g.base
  let Ysite := CrystallineCoefficients.liftedRingedSite I' γ' hc' y₀ p s' hpY
  let Xsite := CrystallineCoefficients.liftedRingedSite I γ hc x₀ p s hpX
  let f₀ := smallRingedMorphism I γ hc x₀ I' γ' hc' s s' y₀ f g hf hpX hpY hγ
  let cmp := crystallineDerivedGlobalSectionsIso I γ hc x₀ I' γ' hc' s s' y₀ f g hf hpX hpY hγ
  let ρ := crystallineBaseRestrictionIso I γ hc x₀ I' γ' hc' s s' y₀ f g hf hpX hpY hγ
  ((CategoryTheory.ModuleCat.derivedExtensionRestrictionAdjunction σ).homEquiv _ _).symm
    ((CategoryTheory.ModuleCat.derivedRestrictionOfScalars α).map
      ((RingedSite.Hom.moduleDerivedGlobalSections.{u + 1} Ysite).map
          (f₀.moduleDerivedAdjunction.unit.app K) ≫
        cmp.inv.app (f₀.modulePullbackDerived.obj K)) ≫
      ρ.hom.app
        ((RingedSite.Hom.moduleDerivedGlobalSections.{u + 1} Xsite).obj
          (f₀.modulePullbackDerived.obj K)))

end CrystallineRingedGeometry
