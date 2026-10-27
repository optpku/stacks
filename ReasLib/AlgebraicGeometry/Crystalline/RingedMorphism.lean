/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.DividedPowers
public import ReasLib.AlgebraicGeometry.Crystalline.RingedSite
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.HomOfCocontinuous
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.HomOfSite
public import ReasLib.CategoryTheory.Sites.Topos.Continuous
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Zariski.Small

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Crystalline.Ringed

variable {p : ℕ} [Fact p.Prime]

/-- Changing the base of a relative crystalline object retains its thickening,
ideal, and divided powers and composes both structure maps. -/
def baseChangeFunctor (B B' : Base.{u} p)
    (g : DividedPowerScheme.Hom B.dividedPowerScheme B'.dividedPowerScheme)
    (f : B.source ⟶ B'.source)
    (hf : f ≫ B'.sourceToClosed = B.sourceToClosed ≫ g.zeroFiberMap) :
    B.bigRingedSite.carrier ⥤ B'.bigRingedSite.carrier where
  obj A :=
    ⟨{ source := (Over.map f).obj A.1.source
       thickening := A.1.thickening
       thickeningToBase := A.1.thickeningToBase ≫ g.base
       inclusion := A.1.inclusion
       ideal := A.1.ideal
       gamma := A.1.gamma
       thickening_compatible := A.1.thickening_compatible
       isThickening := A.1.isThickening
       inclusion_isThickening := A.1.inclusion_isThickening
       ideal_eq_ker := A.1.ideal_eq_ker
       source_comm := sorry }, sorry⟩
  map k :=
    { source := (Over.map f).map k.source
      thickening := k.thickening
      source_comm := k.source_comm
      base_comm := sorry
      ideal_compatible := k.ideal_compatible
      dividedPowers_compatible := k.dividedPowers_compatible }
  map_id := sorry
  map_comp := sorry

/-- Relative crystalline base change lifts covering families of thickenings. -/
theorem baseChangeFunctor_isCocontinuous (B B' : Base.{u} p)
    (g : DividedPowerScheme.Hom B.dividedPowerScheme B'.dividedPowerScheme)
    (f : B.source ⟶ B'.source)
    (hf : f ≫ B'.sourceToClosed = B.sourceToClosed ≫ g.zeroFiberMap) :
    (baseChangeFunctor B B' g f hf).IsCocontinuous
      B.bigRingedSite.siteTopology B'.bigRingedSite.siteTopology := sorry

/-- The inclusion of small crystalline objects into big crystalline objects. -/
abbrev smallInclusion (B : Base.{u} p) : B.ringedSite.carrier ⥤ B.bigRingedSite.carrier :=
  ObjectProperty.ι (smallCrystallineProperty B.scheme B.ideal B.dividedPowers
    B.compatible B.source B.sourceToClosed)

/-- Small crystalline inclusion is continuous for crystalline thickening covers. -/
theorem smallInclusion_isContinuous (B : Base.{u} p) :
    (smallInclusion B).IsContinuous B.ringedSite.siteTopology
      B.bigRingedSite.siteTopology := sorry

/-- Small crystalline inclusion lifts crystalline thickening covers. -/
theorem smallInclusion_isCocontinuous (B : Base.{u} p) :
    (smallInclusion B).IsCocontinuous B.ringedSite.siteTopology
      B.bigRingedSite.siteTopology := sorry

/-- Continuous sheaf pullback along the inclusion of small crystalline objects. -/
abbrev smallInclusionPullback (B : Base.{u} p) :
    Sheaf B.ringedSite.siteTopology (Type (u + 1)) ⥤
      Sheaf B.bigRingedSite.siteTopology (Type (u + 1)) :=
  @Functor.sheafPullback _ _ _ _ (smallInclusion B) (Type (u + 1)) _
    B.ringedSite.siteTopology B.bigRingedSite.siteTopology
    (smallInclusion_isContinuous B) inferInstance

/-- Continuous pullback along small crystalline inclusion is left exact. -/
theorem smallInclusion_pullback_preservesFiniteLimits (B : Base.{u} p) :
    PreservesFiniteLimits (smallInclusionPullback B) := sorry

/-- The continuous projection from the big crystalline topos to the small one. -/
def bigToSmallTopos (B : Base.{u} p) :
    MorphismOfTopoiIn.{u + 1, u + 1, u, u, u + 1}
      B.ringedSite.siteTopology B.bigRingedSite.siteTopology :=
  @Functor.morphismOfTopoiInOfContinuous _ _ _ _ (smallInclusion B)
    B.ringedSite.siteTopology B.bigRingedSite.siteTopology
    (smallInclusion_isContinuous B) inferInstance inferInstance
    (smallInclusion_pullback_preservesFiniteLimits B)

/-- Continuous direct image from the big crystalline site restricts ring sheaves. -/
abbrev bigToSmallRingPush (B : Base.{u} p) :
    Sheaf B.bigRingedSite.siteTopology RingCat.{u + 1} ⥤
      Sheaf B.ringedSite.siteTopology RingCat.{u + 1} :=
  @Functor.sheafPushforwardContinuous _ _ _ _ (smallInclusion B) RingCat.{u + 1} _
    B.ringedSite.siteTopology B.bigRingedSite.siteTopology (smallInclusion_isContinuous B)

/-- Restricting crystalline rings commutes with forgetting their operations. -/
def bigToSmallForgetIso (B : Base.{u} p) :
    bigToSmallRingPush B ⋙
        sheafCompose B.ringedSite.siteTopology (CategoryTheory.forget RingCat.{u + 1}) ≅
      sheafCompose B.bigRingedSite.siteTopology (CategoryTheory.forget RingCat.{u + 1}) ⋙
        (bigToSmallTopos B).pushforward := Iso.refl _

/-- The structure map of big-to-small projection is the identity on thickening functions. -/
def bigToSmallStructureMap (B : Base.{u} p) :
    B.liftedStructureSheaf ⟶ (bigToSmallRingPush B).obj B.bigLiftedStructureSheaf where
  hom := { app := fun A ↦ 𝟙 _, naturality := sorry }

/-- Big-to-small projection preserves the internal ring operations on functions. -/
theorem bigToSmallRingCompatible (B : Base.{u} p) :
    RingedSite.ToposHom.Direct.IsRingCompatible
      (X := B.bigRingedSite) (Y := B.ringedSite) (bigToSmallTopos B)
      (bigToSmallRingPush B) (bigToSmallForgetIso B) (bigToSmallStructureMap B) := sorry

/-- Projection from the big crystalline ringed topos to the small crystalline one. -/
def bigToSmall (B : Base.{u} p) : RingedSite.ToposHom B.bigRingedSite B.ringedSite :=
  RingedSite.ToposHom.ofDirectImage (X := B.bigRingedSite) (Y := B.ringedSite)
    (bigToSmallTopos B) (bigToSmallRingPush B)
    (bigToSmallForgetIso B) (bigToSmallStructureMap B) (bigToSmallRingCompatible B)

/-- The small-to-big structure map retains the same thickening functions. -/
def smallStructureMap (B : Base.{u} p) :
    (smallInclusion B).op ⋙ B.bigLiftedStructureSheaf.obj ⟶ B.liftedStructureSheaf.obj where
  app A := 𝟙 _
  naturality := sorry

/-- Inclusion of the small crystalline ringed topos into the big crystalline one. -/
def smallToBig (B : Base.{u} p) : RingedSite.ToposHom B.ringedSite B.bigRingedSite :=
  @RingedSite.Cocontinuous.toRingedTopos B.ringedSite B.bigRingedSite (smallInclusion B)
    (smallInclusion_isCocontinuous B) inferInstance inferInstance inferInstance inferInstance
    (smallStructureMap B)

/-- Crystalline base change induces the identity map on thickening functions. -/
def bigStructureMap (B B' : Base.{u} p)
    (g : DividedPowerScheme.Hom B.dividedPowerScheme B'.dividedPowerScheme)
    (f : B.source ⟶ B'.source)
    (hf : f ≫ B'.sourceToClosed = B.sourceToClosed ≫ g.zeroFiberMap) :
    (baseChangeFunctor B B' g f hf).op ⋙ B'.bigLiftedStructureSheaf.obj ⟶
      B.bigLiftedStructureSheaf.obj where
  app A := 𝟙 _
  naturality := sorry

/-- A divided-power base map and compatible source map induce a big crystalline
ringed-topos morphism. -/
def bigMorphism (B B' : Base.{u} p)
    (g : DividedPowerScheme.Hom B.dividedPowerScheme B'.dividedPowerScheme)
    (f : B.source ⟶ B'.source)
    (hf : f ≫ B'.sourceToClosed = B.sourceToClosed ≫ g.zeroFiberMap) :
    RingedSite.ToposHom B.bigRingedSite B'.bigRingedSite :=
  @RingedSite.Cocontinuous.toRingedTopos B.bigRingedSite B'.bigRingedSite
    (baseChangeFunctor B B' g f hf) (baseChangeFunctor_isCocontinuous B B' g f hf)
    inferInstance inferInstance inferInstance inferInstance (bigStructureMap B B' g f hf)

/-- A morphism of prime-local divided-power bases and a compatible source square
induce the geometric morphism of small crystalline ringed topoi. -/
def morphism (B B' : Base.{u} p)
    (g : DividedPowerScheme.Hom B.dividedPowerScheme B'.dividedPowerScheme)
    (hbase : g.base ≫ B'.toSpec = B.toSpec) (f : B.source ⟶ B'.source)
    (hf : f ≫ B'.sourceToClosed = B.sourceToClosed ≫ g.zeroFiberMap) :
    RingedSite.ToposHom B.ringedSite B'.ringedSite :=
  RingedSite.ToposHom.comp
    (X := B.ringedSite) (Y := B.bigRingedSite) (Z := B'.ringedSite) (smallToBig B)
    (RingedSite.ToposHom.comp
      (X := B.bigRingedSite) (Y := B'.bigRingedSite) (Z := B'.ringedSite)
      (bigMorphism B B' g f hf) (bigToSmall B'))

/-- The big-to-small Zariski projection retains the functions on each scheme. -/
def baseSmallProjectionSite (S : Scheme.{u}) :
    RingedSite.Hom (Scheme.AssociatedModule.bigCommRingedSite .zariski S)
      (Scheme.AssociatedModule.smallCommRingedSite .zariski S) where
  base := Scheme.Zariski.SmallToBig.relocalizationFunctor (𝟙 S)
  isMorphismOfSites := Scheme.Zariski.SmallToBig.identity_isMorphismOfSites S
  structureSheafMap := { hom := { app := fun A ↦ 𝟙 _, naturality := sorry } }

/-- The projection from the big Zariski ringed topos to the small one. -/
def baseSmallProjection (S : Scheme.{u}) :
    RingedSite.ToposHom (Scheme.AssociatedModule.bigCommRingedSite .zariski S)
      (Scheme.AssociatedModule.smallCommRingedSite .zariski S) :=
  (baseSmallProjectionSite S).toToposHom

/-- Thickening over the crystalline base lifts Zariski covers. -/
theorem bigThickeningOverBase_isCocontinuous (B : Base.{u} p) :
    B.bigThickeningOverBase.IsCocontinuous B.bigRingedSite.siteTopology
      (StandardTopology.zariski.overTopology B.scheme) := sorry

/-- The crystalline structure map is the identity on functions of each thickening. -/
def baseStructureMap (B : Base.{u} p) :
    B.bigThickeningOverBase.op ⋙
        (Scheme.AssociatedModule.bigCommRingedSite .zariski B.scheme).structureSheaf.obj ⟶
      B.bigLiftedStructureSheaf.obj where
  app A := 𝟙 _
  naturality := sorry

/-- The crystalline structure morphism maps to the small Zariski ringed topos
of the divided-power base. -/
def structureMorphism (B : Base.{u} p) :
    RingedSite.ToposHom B.ringedSite
      (Scheme.AssociatedModule.smallCommRingedSite .zariski B.scheme) :=
  RingedSite.ToposHom.comp
    (X := B.ringedSite) (Y := B.bigRingedSite)
    (Z := Scheme.AssociatedModule.smallCommRingedSite .zariski B.scheme) (smallToBig B)
    (RingedSite.ToposHom.comp
      (X := B.bigRingedSite)
      (Y := Scheme.AssociatedModule.bigCommRingedSite .zariski B.scheme)
      (Z := Scheme.AssociatedModule.smallCommRingedSite .zariski B.scheme)
      (@RingedSite.Cocontinuous.toRingedTopos B.bigRingedSite
        (Scheme.AssociatedModule.bigCommRingedSite .zariski B.scheme)
        B.bigThickeningOverBase (bigThickeningOverBase_isCocontinuous B)
        inferInstance inferInstance inferInstance inferInstance (baseStructureMap B))
      (baseSmallProjection B.scheme))

/-- A scheme map induces the lifted small-Zariski ringed-site morphism by
pullback of functions along its geometric inverse-image opens. -/
def zariskiHom {T T' : Scheme.{u}} (f : T ⟶ T') :
    RingedSite.Hom (Scheme.AssociatedModule.smallCommRingedSite .zariski T)
      (Scheme.AssociatedModule.smallCommRingedSite .zariski T') where
  base := Scheme.smallZariskiPullback f
  isMorphismOfSites := sorry
  structureSheafMap :=
    { hom :=
      { app := fun A ↦ RingCat.ofHom
          { toFun := fun s ↦ ULift.up ((pullback.fst A.unop.hom f).appTop.hom s.down)
            map_one' := sorry
            map_mul' := sorry
            map_zero' := sorry
            map_add' := sorry }
        naturality := sorry } }

/-- Pullback on lifted Zariski functions is induced by the pullback projection. -/
theorem zariskiHom_app {T T' : Scheme.{u}} (f : T ⟶ T')
    (A : T'.smallZariskiSiteᵒᵖ)
    (s : (Scheme.AssociatedModule.smallCommRingedSite .zariski T').structureSheaf.obj.obj A) :
    (zariskiHom f).structureSheafMap.hom.app A s =
      ULift.up ((pullback.fst A.unop.hom f).appTop.hom s.down) := sorry

end AlgebraicGeometry.Scheme.Crystalline.Ringed
