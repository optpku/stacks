/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap60.Remark_60_24_1_Higher_direct_images_Context
public import stacks_project.Chap60.Remark_60_24_9_Base_change_isomorphism_RingedGeometry
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open RingedSite RingedSite.Hom
open AlgebraicGeometry.Scheme.Crystalline

noncomputable section

universe u

namespace CrystallineEvaluation

/-- The lifted source structure sheaf and its small crystalline site. -/
abbrev source (c : HigherDirectImageContext.{u}) : RingedSite.{u + 1, u, u + 1} :=
  CrystallineCoefficients.liftedRingedSite c.S.ideal c.S.dividedPowers c.S.compatible
    c.x₀ c.p c.s c.pX

/-- The lifted target structure sheaf and its small crystalline site. -/
abbrev target (c : HigherDirectImageContext.{u}) : RingedSite.{u + 1, u, u + 1} :=
  CrystallineCoefficients.liftedRingedSite c.S'.ideal c.S'.dividedPowers c.S'.compatible
    c.x'₀ c.p c.s' c.pX'

/-- The ringed crystalline topos morphism induced by the geometric square. -/
def directImage (c : HigherDirectImageContext.{u}) : ToposHom (source c) (target c) :=
  CrystallineRingedGeometry.smallRingedMorphism c.S.ideal c.S.dividedPowers c.S.compatible
    c.x₀ c.S'.ideal c.S'.dividedPowers c.S'.compatible c.s c.s' c.x'₀ c.fSch
    c.setupHom c.h_comm c.pX c.pX' c.g.dividedPowers_compatible

/-- The open subscheme pulled back from the source of the target thickening. -/
abbrev openSource (c : HigherDirectImageContext.{u}) : Scheme.{u} :=
  pullback c.fSch c.T'.obj.1.source.hom

/-- The divided-power scheme actually carried by the target crystalline object. -/
def targetDividedPowers (c : HigherDirectImageContext.{u}) : DividedPowerScheme.{u} where
  scheme := c.T'.obj.1.thickening
  ideal := c.T'.obj.1.ideal
  quasiCoherent := sorry
  dividedPowers := c.T'.obj.1.gamma
  compatible := c.T'.obj.1.thickening_compatible

/-- The trivial divided-power scheme on the pulled-back open subscheme. -/
def zeroScheme (c : HigherDirectImageContext.{u}) : DividedPowerScheme.{u} where
  scheme := openSource c
  ideal := ⊥
  quasiCoherent := sorry
  dividedPowers := fun affine ↦
    (congrFun Scheme.IdealSheafData.ideal_bot affine).symm ▸ dividedPowersBot Γ(openSource c, affine)
  compatible := sorry

/-- The zero-ideal source maps to the original divided-power base. -/
def sourceToBase (c : HigherDirectImageContext.{u}) :
    DividedPowerScheme.Hom (zeroScheme c) c.S where
  base := pullback.fst c.fSch c.T'.obj.1.source.hom ≫ c.x₀ ≫ c.S.ideal.subschemeι
  ideal_compatible := sorry
  dividedPowers_compatible := sorry

/-- The zero-ideal source maps to the target thickening. -/
def sourceToTarget (c : HigherDirectImageContext.{u})
    (targetIdentification : c.T'thick = targetDividedPowers c) :
    DividedPowerScheme.Hom (zeroScheme c) c.T'thick where
  base := pullback.snd c.fSch c.T'.obj.1.source.hom ≫ c.T'.obj.1.inclusion ≫
    eqToHom c.h_T'thick.symm
  ideal_compatible := sorry
  dividedPowers_compatible := sorry

/-- The two source maps commute over the target base. -/
theorem sourceSquare (c : HigherDirectImageContext.{u})
    (targetIdentification : c.T'thick = targetDividedPowers c) :
    DividedPowerScheme.Hom.comp (sourceToTarget c targetIdentification) c.πT' =
      DividedPowerScheme.Hom.comp (sourceToBase c) c.g := sorry

/-- The divided-power pullback supplies the actual map from the open source to `T`. -/
def sourceToPullback (c : HigherDirectImageContext.{u})
    (targetIdentification : c.T'thick = targetDividedPowers c) :
    DividedPowerScheme.Hom (zeroScheme c) c.Tthick :=
  c.h_cart.lift (sourceToTarget c targetIdentification) (sourceToBase c)
    (sourceSquare c targetIdentification)

/-- The induced source map to the zero fibre of the divided-power pullback. -/
def sourceToZeroFiber (c : HigherDirectImageContext.{u})
    (targetIdentification : c.T'thick = targetDividedPowers c) :
    openSource c ⟶ c.Tthick.ideal.subscheme :=
  inv (Scheme.IdealSheafData.subschemeι (⊥ : (openSource c).IdealSheafData)) ≫
    (sourceToPullback c targetIdentification).zeroFiberMap

/-- Local nilpotence restricts to the inverse-image open subscheme. -/
theorem openSource_nilpotent (c : HigherDirectImageContext.{u}) :
    ∀ affine : (openSource c).affineOpens, IsNilpotent (c.p : Γ(openSource c, affine)) := sorry

/-- The actual crystalline site of the open source over the divided-power pullback.
The map `U ⟶ T₀` is a structure map; `(U,T)` is not required to be an object of `Cris(X/S)`. -/
abbrev pullbackSite (c : HigherDirectImageContext.{u})
    (targetIdentification : c.T'thick = targetDividedPowers c) :
    RingedSite.{u + 1, u, u + 1} :=
  CrystallineCoefficients.liftedRingedSite c.Tthick.ideal c.Tthick.dividedPowers
    c.Tthick.compatible (sourceToZeroFiber c targetIdentification) c.p (c.πT.base ≫ c.s)
      (openSource_nilpotent c)

/-- The induced divided-power setup morphism from `T` to `S`. -/
def pullbackSetup (c : HigherDirectImageContext.{u}) :
    DividedPowerSchemeHom c.Tthick.ideal c.S.ideal (c.πT.base ≫ c.s) c.s :=
  DividedPowerSchemeHom.of c.πT.base c.πT.zeroFiberMap
    (DividedPowerScheme.Hom.zeroFiberMap_comm c.πT) sorry c.πT.ideal_compatible

/-- The inverse-image open subscheme commutes with the divided-power zero fibres. -/
theorem restrictionSquare (c : HigherDirectImageContext.{u})
    (targetIdentification : c.T'thick = targetDividedPowers c) :
    pullback.fst c.fSch c.T'.obj.1.source.hom ≫ c.x₀ =
      sourceToZeroFiber c targetIdentification ≫ (pullbackSetup c).zeroFiberMap := sorry

/-- The crystalline morphism `Cris(U/T) ⟶ Cris(X/S)` induced by the pullback square. -/
def restriction (c : HigherDirectImageContext.{u})
    (targetIdentification : c.T'thick = targetDividedPowers c) :
    ToposHom (pullbackSite c targetIdentification) (source c) :=
  CrystallineRingedGeometry.smallRingedMorphism c.Tthick.ideal c.Tthick.dividedPowers
    c.Tthick.compatible (sourceToZeroFiber c targetIdentification)
    c.S.ideal c.S.dividedPowers c.S.compatible (c.πT.base ≫ c.s) c.s c.x₀
    (pullback.fst c.fSch c.T'.obj.1.source.hom) (pullbackSetup c)
    (restrictionSquare c targetIdentification) (openSource_nilpotent c) c.pX
    c.πT.dividedPowers_compatible

/-- The genuine structure morphism of `Cris(U/T)` to the Zariski site of `T`. -/
def structureMorphism (c : HigherDirectImageContext.{u})
    (targetIdentification : c.T'thick = targetDividedPowers c) :
    ToposHom (pullbackSite c targetIdentification)
      (Scheme.AssociatedModule.smallCommRingedSite .zariski c.Tthick.scheme) :=
  CrystallineRingedGeometry.structureMorphismToSmall c.Tthick.ideal
    c.Tthick.dividedPowers c.Tthick.compatible (sourceToZeroFiber c targetIdentification)
    (c.πT.base ≫ c.s) (openSource_nilpotent c)

/-- The target crystalline slice retains its actual maps of thickenings. -/
def sliceThickening (c : HigherDirectImageContext.{u}) :
    (target c).localization c.T' ⥤ Over c.T'thick.scheme where
  obj test := Over.mk (CrystallineObject.Hom.thickening test.hom.hom ≫
    eqToHom c.h_T'thick.symm)
  map map := Over.homMk (CrystallineObject.Hom.thickening map.left.hom) sorry
  map_id := sorry
  map_comp := sorry

/-- Restriction to an open covering of a thickening gives a covering in its crystalline slice. -/
instance sliceThickening_isCocontinuous (c : HigherDirectImageContext.{u}) :
    (sliceThickening c).IsCocontinuous ((target c).localization c.T').siteTopology
      c.T'thick.scheme.bigZariskiTopology := sorry

/-- Evaluation uses the same functions on every test thickening, not an arbitrary ring map. -/
def evaluationStructureMap (c : HigherDirectImageContext.{u}) :
    (sliceThickening c).op ⋙
        (Scheme.AssociatedModule.bigCommRingedSite .zariski c.T'thick.scheme).structureSheaf.obj ⟶
      ((target c).localization c.T').structureSheaf.obj where
  app test := 𝟙 _
  naturality := sorry

/-- The thickening evaluation morphism, constructed from the target crystalline slice. -/
def evaluation (c : HigherDirectImageContext.{u}) :
    ToposHom ((target c).localization c.T')
      (Scheme.AssociatedModule.smallCommRingedSite .zariski c.T'thick.scheme) :=
  @RingedSite.ToposHom.comp
    ((target c).localization c.T')
    (Scheme.AssociatedModule.bigCommRingedSite .zariski c.T'thick.scheme)
    (Scheme.AssociatedModule.smallCommRingedSite .zariski c.T'thick.scheme)
    inferInstance inferInstance inferInstance
    (@RingedSite.Cocontinuous.toRingedTopos
      ((target c).localization c.T')
      (Scheme.AssociatedModule.bigCommRingedSite .zariski c.T'thick.scheme)
      (sliceThickening c) inferInstance inferInstance inferInstance inferInstance inferInstance
      (evaluationStructureMap c))
    (CrystallineRingedGeometry.baseSmallProjection c.T'thick.scheme)

/-- The Zariski map between the actual pullback and target thickenings. -/
def zariski (c : HigherDirectImageContext.{u}) :
    RingedSite.Hom (Scheme.AssociatedModule.smallCommRingedSite .zariski c.Tthick.scheme)
      (Scheme.AssociatedModule.smallCommRingedSite .zariski c.T'thick.scheme) where
  base := Scheme.smallZariskiPullback c.iDP.base
  isMorphismOfSites := sorry
  structureSheafMap :=
    { hom :=
      { app := fun test ↦ RingCat.ofHom
          { toFun := fun function ↦ ULift.up
              ((pullback.fst test.unop.hom c.iDP.base).appTop.hom function.down)
            map_one' := sorry
            map_mul' := sorry
            map_zero' := sorry
            map_add' := sorry }
        naturality := sorry } }

/-- Source structure rings are the canonical lifts of functions on thickenings. -/
theorem source_sections (c : HigherDirectImageContext.{u}) (test : source c) :
    (source c).structureSheaf.obj.obj (op test) =
      RingCat.of (ULift.{u + 1, u} Γ(test.obj.1.thickening, ⊤)) := sorry

/-- Target structure rings are the canonical lifts of functions on thickenings. -/
theorem target_sections (c : HigherDirectImageContext.{u}) (test : target c) :
    (target c).structureSheaf.obj.obj (op test) =
      RingCat.of (ULift.{u + 1, u} Γ(test.obj.1.thickening, ⊤)) := sorry

/-- The crystalline direct image uses the geometric morphism and its canonical ring map. -/
theorem directImage_def (c : HigherDirectImageContext.{u}) :
    directImage c =
      CrystallineRingedGeometry.smallRingedMorphism c.S.ideal c.S.dividedPowers c.S.compatible
        c.x₀ c.S'.ideal c.S'.dividedPowers c.S'.compatible c.s c.s' c.x'₀ c.fSch
        c.setupHom c.h_comm c.pX c.pX' c.g.dividedPowers_compatible := sorry

/-- The scheme underlying `U` is the geometric inverse image of the open source `U′`. -/
theorem openSource_isPullback (c : HigherDirectImageContext.{u}) :
    IsPullback (pullback.fst c.fSch c.T'.obj.1.source.hom)
      (pullback.snd c.fSch c.T'.obj.1.source.hom) c.fSch c.T'.obj.1.source.hom := sorry

/-- The target divided powers are exactly those of the chosen crystalline object. -/
theorem targetDividedPowers_gamma (c : HigherDirectImageContext.{u})
    (affine : c.T'.obj.1.thickening.affineOpens) :
    (targetDividedPowers c).dividedPowers affine = c.T'.obj.1.gamma affine := sorry

/-- The auxiliary divided-power structure is on the zero ideal, not an invented thickening. -/
theorem zeroScheme_ideal (c : HigherDirectImageContext.{u}) :
    (zeroScheme c).ideal = ⊥ := sorry

/-- The auxiliary source-to-base morphism has the prescribed scheme map. -/
theorem sourceToBase_base (c : HigherDirectImageContext.{u}) :
    (sourceToBase c).base =
      pullback.fst c.fSch c.T'.obj.1.source.hom ≫ c.x₀ ≫ c.S.ideal.subschemeι := sorry

/-- The auxiliary source-to-target morphism is induced by the target inclusion. -/
theorem sourceToTarget_base (c : HigherDirectImageContext.{u})
    (targetIdentification : c.T'thick = targetDividedPowers c) :
    (sourceToTarget c targetIdentification).base =
      pullback.snd c.fSch c.T'.obj.1.source.hom ≫ c.T'.obj.1.inclusion ≫
        eqToHom c.h_T'thick.symm := sorry

/-- The canonical divided-power lift has the prescribed target projection. -/
theorem sourceToPullback_fst (c : HigherDirectImageContext.{u})
    (targetIdentification : c.T'thick = targetDividedPowers c) :
    DividedPowerScheme.Hom.comp (sourceToPullback c targetIdentification) c.iDP =
      sourceToTarget c targetIdentification := sorry

/-- The canonical divided-power lift has the prescribed base projection. -/
theorem sourceToPullback_snd (c : HigherDirectImageContext.{u})
    (targetIdentification : c.T'thick = targetDividedPowers c) :
    DividedPowerScheme.Hom.comp (sourceToPullback c targetIdentification) c.πT =
      sourceToBase c := sorry

/-- The induced zero-fibre map agrees with the original source map after projection to `S₀`. -/
theorem sourceToZeroFiber_comm (c : HigherDirectImageContext.{u})
    (targetIdentification : c.T'thick = targetDividedPowers c) :
    sourceToZeroFiber c targetIdentification ≫ c.πT.zeroFiberMap =
      pullback.fst c.fSch c.T'.obj.1.source.hom ≫ c.x₀ := sorry

/-- Functions on the pullback crystalline site are functions on its own thickenings. -/
theorem pullbackSite_sections (c : HigherDirectImageContext.{u})
    (targetIdentification : c.T'thick = targetDividedPowers c)
    (test : pullbackSite c targetIdentification) :
    (pullbackSite c targetIdentification).structureSheaf.obj.obj (op test) =
      RingCat.of (ULift.{u + 1, u} Γ(test.obj.1.thickening, ⊤)) := sorry

/-- The setup map of the restriction is the given divided-power projection `T ⟶ S`. -/
theorem pullbackSetup_base (c : HigherDirectImageContext.{u}) :
    (pullbackSetup c).base = c.πT.base := sorry

/-- Module restriction is geometric inverse image followed by canonical scalar extension. -/
theorem restriction_modules (c : HigherDirectImageContext.{u})
    (targetIdentification : c.T'thick = targetDividedPowers c)
    [(SheafOfModules.restrictScalars (restriction c targetIdentification).structureMap).IsRightAdjoint] :
    (restriction c targetIdentification).modulePullback =
      (restriction c targetIdentification).toTopos.moduleInverseImage (source c).structureSheaf ⋙
        SheafOfModules.ChangeOfRings.extendScalars
          (restriction c targetIdentification).structureMap := sorry

/-- The structure morphism is the canonical crystalline-to-Zariski morphism of `U/T`. -/
theorem structureMorphism_def (c : HigherDirectImageContext.{u})
    (targetIdentification : c.T'thick = targetDividedPowers c) :
    structureMorphism c targetIdentification =
      CrystallineRingedGeometry.structureMorphismToSmall c.Tthick.ideal
        c.Tthick.dividedPowers c.Tthick.compatible (sourceToZeroFiber c targetIdentification)
        (c.πT.base ≫ c.s) (openSource_nilpotent c) := sorry

/-- Each evaluation test retains its actual thickening over `T′`. -/
theorem sliceThickening_obj (c : HigherDirectImageContext.{u})
    (test : (target c).localization c.T') :
    (sliceThickening c).obj test =
      Over.mk (CrystallineObject.Hom.thickening test.hom.hom ≫
        eqToHom c.h_T'thick.symm) := sorry

/-- Evaluation does not change the functions on a test thickening. -/
theorem evaluationStructureMap_app (c : HigherDirectImageContext.{u})
    (test : ((target c).localization c.T')ᵒᵖ) :
    (evaluationStructureMap c).app test = 𝟙 _ := sorry

/-- The evaluation morphism is induced by the actual slice-thickening functor. -/
theorem evaluation_toTopos (c : HigherDirectImageContext.{u}) :
    (evaluation c).toTopos = MorphismOfTopoiIn.comp
      (CrystallineRingedGeometry.baseSmallProjection c.T'thick.scheme).toTopos
      (@RingedSite.Cocontinuous.toTopos ((target c).localization c.T')
        (Scheme.AssociatedModule.bigCommRingedSite .zariski c.T'thick.scheme)
        (sliceThickening c) inferInstance inferInstance inferInstance) := sorry

/-- Thickening evaluation is left exact on modules. -/
instance evaluation_preservesFiniteLimits (c : HigherDirectImageContext.{u}) :
    PreservesFiniteLimits (evaluation c).modulePushforward := sorry

/-- Thickening evaluation is right exact on modules, so its derived functor is restriction. -/
instance evaluation_preservesFiniteColimits (c : HigherDirectImageContext.{u}) :
    PreservesFiniteColimits (evaluation c).modulePushforward := sorry

/-- The Zariski comparison is induced by the actual map between the thickenings. -/
theorem zariski_base (c : HigherDirectImageContext.{u}) :
    (zariski c).base = Scheme.smallZariskiPullback c.iDP.base := sorry

end CrystallineEvaluation

/-- The single complex in degree zero for the canonical module coefficient universe. -/
abbrev degreeZeroModule (site : RingedSite.{u + 1, u, u + 1}) :
    ModuleCat.{u + 1} site ⥤ ModuleDerived.{u + 1} site :=
  @DerivedCategory.singleFunctor
    (ModuleCat.{u + 1} site) inferInstance inferInstance
    (moduleCat_hasDerivedCategory.{u + 1} site) 0

/-- The module embedding is the canonical single-complex functor in degree zero. -/
theorem degreeZeroModule_eq (site : RingedSite.{u + 1, u, u + 1}) :
    degreeZeroModule site =
      @DerivedCategory.singleFunctor (ModuleCat.{u + 1} site) inferInstance inferInstance
        (moduleCat_hasDerivedCategory.{u + 1} site) 0 := sorry

open CrystallineEvaluation

/-- 60.24.1.1: evaluation of the crystalline derived direct image on `T′`
agrees with derived pushforward through `Cris(U/T)` and the Zariski map
`T ⟶ T′`, where `U = X ×[X′] U′` and `T` is the divided-power pullback.
The target identification fixes the divided powers on the actual target
thickening; no factorization maps or comparison isomorphisms are inputs.
Structure rings are canonically universe-lifted for the ringed-topos API. -/
@[stacks 07MK]
theorem crystallinePushforwardEvalIso
    (c : HigherDirectImageContext.{u})
    (targetIdentification : c.T'thick = targetDividedPowers c)
    [(SheafOfModules.restrictScalars (restriction c targetIdentification).structureMap).IsRightAdjoint]
    [(directImage c).HasModulePushforwardDerived]
    [(structureMorphism c targetIdentification).HasModulePushforwardDerived]
    [(evaluation c).HasModulePushforwardDerived]
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u + 1} (zariski c))
      (ModuleQis.{u + 1}
        (Scheme.AssociatedModule.smallCommRingedSite .zariski c.Tthick.scheme))]
    (F : ModuleCat.{u + 1} (source c)) :
    IsIsomorphic
      ((evaluation c).modulePushforwardDerived.obj
        ((localizedRestrictionDerived.{u + 1} (target c) c.T').obj
          ((directImage c).modulePushforwardDerived.obj
            ((degreeZeroModule (source c)).obj F))))
      ((modulePushforwardDerived.{u + 1} (zariski c)).obj
        ((structureMorphism c targetIdentification).modulePushforwardDerived.obj
          ((degreeZeroModule (pullbackSite c targetIdentification)).obj
            ((restriction c targetIdentification).modulePullback.obj F)))) := sorry
