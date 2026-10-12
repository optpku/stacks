/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SheafAdjunction
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.ModuleAdjunction

@[expose] public section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.AlgebraicSpace
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.EtaleRingedTopos
variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- The constructed geometric inverse image is left exact. This is the usual
left-exactness law for the étale base-change construction. -/
instance leftExact (f : X ⟶ Y) :
    PreservesFiniteLimits (AlgebraicGeometry.AlgebraicSpace.EtaleTopos.inverseImage f) := sorry

/-- The morphism of topoi retains the actual constructed adjunction. -/
def topos (f : X ⟶ Y) : MorphismOfTopoiIn (smallEtaleTopology Y) (smallEtaleTopology X) where
  inverseImageFunctor := LeftExactFunctor.of (AlgebraicGeometry.AlgebraicSpace.EtaleTopos.inverseImage f)
  pushforward := AlgebraicGeometry.AlgebraicSpace.EtaleTopos.directImage f
  adjunction := AlgebraicGeometry.AlgebraicSpace.EtaleTopos.adjunction f

/-- The structure sheaf with its actual underlying section types. -/
def structureTypes (X : AlgebraicSpace S) : Sheaf (smallEtaleTopology X) (Type u) :=
  (sheafCompose (smallEtaleTopology X) (forget RingCat.{u})).obj (structureSheaf X)

/-- A small-chart arrow into a fiber product induces its actual scheme map to the target chart. -/
def schemeMap (f : X ⟶ Y) (b : smallEtaleSite Y)
    (a : StructuredArrow (op ((etaleBaseChange f).obj b))
      (AlgebraicGeometry.AlgebraicSpace.SpacesEtale.AtlasCharts.inclusion X).op) :
    (AlgebraicGeometry.AlgebraicSpace.SmallEtale.AtlasCharts.object X a.right.unop).left ⟶ b.left :=
  yonedaEquiv (a.hom.unop.left ≫ etaleBaseChangeSnd f b)

/-- The section cone sends a scalar to its pullback along each explicit scheme map. -/
def structureCone (f : X ⟶ Y) (b : smallEtaleSite Y) :
    Cone (StructuredArrow.proj (op ((etaleBaseChange f).obj b))
      (AlgebraicGeometry.AlgebraicSpace.SpacesEtale.AtlasCharts.inclusion X).op ⋙
        ((AlgebraicGeometry.AlgebraicSpace.EtaleTopos.smallEquivalence X).functor.obj (structureTypes X)).obj) where
  pt := (structureTypes Y).obj.obj (op b)
  π :=
    { app := fun a ↦ TypeCat.ofHom (schemeMap f b a).left.appTop.hom
      naturality := sorry }

/-- The structure map on every target chart is an actual small-limit lift. -/
def structureUnderlying (f : X ⟶ Y) :
    structureTypes Y ⟶ (AlgebraicGeometry.AlgebraicSpace.EtaleTopos.directImage f).obj (structureTypes X) where
  hom :=
    { app := fun b ↦ limit.lift _ (structureCone f b.unop) ≫
        ((AlgebraicGeometry.AlgebraicSpace.SpacesEtale.AtlasCharts.inclusion X).op.ranObjObjIsoLimit
          ((AlgebraicGeometry.AlgebraicSpace.EtaleTopos.smallEquivalence X).functor.obj (structureTypes X)).obj
          (op ((etaleBaseChange f).obj b.unop))).inv
      naturality := sorry }

/-- Ring direct image is the canonical internal-ring lift of the constructed direct image. -/
def ringPushforward (f : X ⟶ Y) :
    Sheaf (smallEtaleTopology X) RingCat.{u} ⥤ Sheaf (smallEtaleTopology Y) RingCat.{u} :=
  (topos f).ringDirectImage

/-- Its underlying sheaf comparison is the canonical ring reconstruction comparison. -/
def forgetIso (f : X ⟶ Y) :
    ringPushforward f ⋙ sheafCompose (smallEtaleTopology Y) (forget RingCat.{u}) ≅
      sheafCompose (smallEtaleTopology X) (forget RingCat.{u}) ⋙
        AlgebraicGeometry.AlgebraicSpace.EtaleTopos.directImage f :=
  (topos f).ringDirectImageForgetIso

/-- The ring-valued structure map has the same section functions as the geometric map. -/
def structureMap (f : X ⟶ Y) :
    structureSheaf Y ⟶ (ringPushforward f).obj (structureSheaf X) where
  hom :=
    { app := fun U ↦ @RingCat.ofHom
        ((structureSheaf Y).obj.obj U)
        (((ringPushforward f).obj (structureSheaf X)).obj.obj U) _ _
        { toFun := ((structureUnderlying f ≫ (forgetIso f).inv.app (structureSheaf X)).hom.app U)
          map_one' := sorry
          map_mul' := sorry
          map_zero' := sorry
          map_add' := sorry }
      naturality := sorry }

/-- The ringed-topos map uses the actual constructed direct-image map and adjunction. -/
def ringedHom (f : X ⟶ Y) : RingedSite.ToposHom (ringedSite X) (ringedSite Y) :=
  @RingedSite.ToposHom.ofDirectImage (ringedSite X) (ringedSite Y) _ _
    (topos f) (ringPushforward f) (forgetIso f) (structureMap f) sorry

/-- Ring-valued extension uses actual limits on the essentially small chart index. -/
def ringChartLimits (X : AlgebraicSpace S) (U : (spacesEtaleSite X)ᵒᵖ) :
    HasLimitsOfShape (StructuredArrow U (SpacesEtale.AtlasCharts.inclusion X).op) RingCat.{u} :=
  hasLimitsOfShape_of_essentiallySmall.{u} _ _

/-- The small chart presentation for ring sheaves uses the constructed Kan adjunction. -/
def ringSmallEquivalence (X : AlgebraicSpace S) :
    Sheaf (smallEtaleTopology X) RingCat.{u} ≌
      Sheaf (SmallEtale.AtlasCharts.topology X) RingCat.{u} := by
  -- Local instance justification (defeq pin): fix the genuine small ring limits used by the chart restriction and its Kan right adjoint.
  letI (U : (smallEtaleSite X)ᵒᵖ) :
      HasLimitsOfShape (StructuredArrow U (SmallEtale.AtlasCharts.inclusion X).op) RingCat.{u} :=
    hasLimitsOfShape_of_essentiallySmall.{u} _ _
  exact ((SmallEtale.AtlasCharts.inclusion X).sheafAdjunctionCocontinuous RingCat.{u}
    (SmallEtale.AtlasCharts.topology X) (smallEtaleTopology X)).toEquivalence

/-- Ring sheaves on the spaces-étale site have the same explicit small-chart presentation. -/
def ringSpaceEquivalence (X : AlgebraicSpace S) :
    Sheaf (spacesEtaleTopology X) RingCat.{u} ≌
      Sheaf (SmallEtale.AtlasCharts.topology X) RingCat.{u} := by
  -- Local instance justification (defeq pin): retain the specified ring limits when constructing the spaces-chart Kan unit and counit.
  letI := ringChartLimits X
  exact ((SpacesEtale.AtlasCharts.inclusion X).sheafAdjunctionCocontinuous RingCat.{u}
    (SpacesEtale.AtlasCharts.topology X) (spacesEtaleTopology X)).toEquivalence

/-- Extend a ring sheaf through small charts, retaining its ring operations and restriction maps. -/
def ringExtension (X : AlgebraicSpace S) :
    Sheaf (smallEtaleTopology X) RingCat.{u} ⥤ Sheaf (spacesEtaleTopology X) RingCat.{u} :=
  (ringSmallEquivalence X).functor ⋙ (ringSpaceEquivalence X).inverse

/-- The small-chart counit identifies restriction of the constructed ring extension. -/
def ringExtensionRestrictionIso (X : AlgebraicSpace S) :
    ringExtension X ⋙ (smallEtaleInclusion X).sheafPushforwardContinuous RingCat.{u}
      (smallEtaleTopology X) (spacesEtaleTopology X) ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun N ↦
      let e := (ringSpaceEquivalence X).counitIso.app ((ringSmallEquivalence X).functor.obj N)
      let i : (SmallEtale.AtlasCharts.inclusion X).op ⋙
          (((smallEtaleInclusion X).sheafPushforwardContinuous RingCat.{u}
            (smallEtaleTopology X) (spacesEtaleTopology X)).obj ((ringExtension X).obj N)).obj ≅
          (SmallEtale.AtlasCharts.inclusion X).op ⋙ N.obj :=
        { hom := e.hom.hom, inv := e.inv.hom, hom_inv_id := sorry, inv_hom_id := sorry }
      Functor.IsCoverDense.sheafIso i)
    sorry

/-- Evaluate the ring extension on an actual scheme chart by restriction and the small-chart counit. -/
def ringExtensionEvaluation (X : AlgebraicSpace S) (Q : Sheaf (smallEtaleTopology X) RingCat.{u})
    {W : spacesEtaleSite X} {U : smallEtaleSite X}
    (a : (smallEtaleInclusion X).obj U ⟶ W) :
    ((ringExtension X).obj Q).obj.obj (op W) ⟶ Q.obj.obj (op U) :=
  ((ringExtension X).obj Q).obj.map a.op ≫
    ((ringExtensionRestrictionIso X).hom.app Q).hom.app (op U)

/-- Restrict a cone over all scheme charts to the supplied small chart family. -/
def ringExtensionSmallCone (X : AlgebraicSpace S) (Q : Sheaf (smallEtaleTopology X) RingCat.{u})
    (W : spacesEtaleSite X)
    (c : Cone (StructuredArrow.proj (op W) (smallEtaleInclusion X).op ⋙ Q.obj)) :
    Cone (StructuredArrow.proj (op W) (SpacesEtale.AtlasCharts.inclusion X).op ⋙
      ((ringSmallEquivalence X).functor.obj Q).obj) where
  pt := c.pt
  π :=
    { app := fun a ↦ c.π.app
        (StructuredArrow.mk (Y := op ((SmallEtale.AtlasCharts.inclusion X).obj a.right.unop)) a.hom)
      naturality := sorry }

/-- Lift an actual cone of ring maps into the small-chart extension, using genuine small limits. -/
def ringExtensionLift (X : AlgebraicSpace S) (Q : Sheaf (smallEtaleTopology X) RingCat.{u})
    (W : spacesEtaleSite X)
    (c : Cone (StructuredArrow.proj (op W) (smallEtaleInclusion X).op ⋙ Q.obj)) :
    c.pt ⟶ ((ringExtension X).obj Q).obj.obj (op W) := by
  -- Local instance justification (defeq pin): the limit lift uses exactly the ring limits chosen for the explicit spaces-chart extension.
  letI := ringChartLimits X
  exact limit.lift _ (ringExtensionSmallCone X Q W c) ≫
    ((SpacesEtale.AtlasCharts.inclusion X).op.ranObjObjIsoLimit
      ((ringSmallEquivalence X).functor.obj Q).obj (op W)).inv

/-- Pullback of regular functions into every small chart over the actual fibre product. -/
def ringStructureCone (f : X ⟶ Y) (b : smallEtaleSite Y) :
    Cone (StructuredArrow.proj (op ((etaleBaseChange f).obj b))
      (SpacesEtale.AtlasCharts.inclusion X).op ⋙
        ((ringSmallEquivalence X).functor.obj (structureSheaf X)).obj) where
  pt := (structureSheaf Y).obj.obj (op b)
  π :=
    { app := fun a ↦ (forget₂ CommRingCat RingCat).map (schemeMap f b a).left.appTop
      naturality := sorry }

/-- The structure map into the ring extension is the actual small-limit lift of scheme maps. -/
def ringExtensionStructureMap (f : X ⟶ Y) :
    structureSheaf Y ⟶ ((etaleBaseChange f).sheafPushforwardContinuous RingCat.{u}
      (smallEtaleTopology Y) (spacesEtaleTopology X)).obj
        ((ringExtension X).obj (structureSheaf X)) := by
  -- Local instance justification (defeq pin): use the same small ring limits as ringSpaceEquivalence, so the lift lands in that exact extension.
  letI := ringChartLimits X
  exact ⟨{
    app := fun b ↦ limit.lift _ (ringStructureCone f b.unop) ≫
      ((SpacesEtale.AtlasCharts.inclusion X).op.ranObjObjIsoLimit
        ((ringSmallEquivalence X).functor.obj (structureSheaf X)).obj
        (op ((etaleBaseChange f).obj b.unop))).inv
    naturality := sorry }⟩

end AlgebraicGeometry.AlgebraicSpace.EtaleRingedTopos
