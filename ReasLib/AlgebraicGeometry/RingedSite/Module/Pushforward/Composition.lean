module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pushforward
import Mathlib.Tactic.CrossRefAttribute

/-!
# Composition of module pushforwards on ringed sites

This leaf exposes the pseudofunctorial composition isomorphism for direct images of module
sheaves.  It is the underived comparison used by derived composition and base-change APIs.
-/

@[expose] public section

open CategoryTheory

noncomputable section

namespace RingedSite.Hom

/-- Direct image along a composite ringed-site morphism is canonically isomorphic to the
composite of the two direct-image functors. -/
@[stacks 03D8 "(1)"]
noncomputable def modulePushforwardCompIso.{z, uX, vX, uY, vY, uZ, vZ, w}
    {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
    {Z : RingedSite.{uZ, vZ, w}} (f : Hom X Y) (g : Hom Y Z) :
    f.modulePushforward.{z} ⋙ g.modulePushforward.{z} ≅
      (Hom.comp f g).modulePushforward.{z} :=
  @SheafOfModules.pushforwardComp.{z} _ _ _ _ _ _
    Z.siteTopology Y.siteTopology g.base Z.structureSheaf Y.structureSheaf
    g.base_isContinuous g.structureSheafMap X.siteTopology f.base X.structureSheaf
    f.base_isContinuous f.structureSheafMap

/-- A composite module pushforward is automatically a right adjoint when both constituent
pushforwards are right adjoints. -/
@[stacks 03D8 "right adjoint composition"]
instance modulePushforwardComp_isRightAdjoint.{z, uX, vX, uY, vY, uZ, vZ, w}
    {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
    {Z : RingedSite.{uZ, vZ, w}} (f : Hom X Y) (g : Hom Y Z)
    [(f.modulePushforward.{z}).IsRightAdjoint]
    [(g.modulePushforward.{z}).IsRightAdjoint] :
    ((Hom.comp f g).modulePushforward.{z}).IsRightAdjoint :=
  Functor.isRightAdjoint_of_iso (modulePushforwardCompIso f g)

namespace CommRingPresentation

/-- The right-adjoint instance for a composite module pushforward remains visible when all
three ringed sites are presented by commutative ring sheaves.  This anchors the generic
composition instance across the reducible `ofCommRingSheaf` presentation. -/
@[stacks 03D8 "commutative presentation right adjoint composition"]
instance modulePushforwardCompIsRightAdjoint.{z, uX, vX, uY, vY, uZ, vZ, w}
    {C : Type uX} [Category.{vX} C]
    {D : Type uY} [Category.{vY} D]
    {E : Type uZ} [Category.{vZ} E]
    {JX : GrothendieckTopology C} {JY : GrothendieckTopology D}
    {JZ : GrothendieckTopology E}
    [JX.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [JY.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [JZ.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    {OX : Sheaf JX CommRingCat.{w}} {OY : Sheaf JY CommRingCat.{w}}
    {OZ : Sheaf JZ CommRingCat.{w}}
    (f : Hom (RingedSite.ofCommRingSheaf JX OX)
      (RingedSite.ofCommRingSheaf JY OY))
    (g : Hom (RingedSite.ofCommRingSheaf JY OY)
      (RingedSite.ofCommRingSheaf JZ OZ))
    [(f.modulePushforward.{z}).IsRightAdjoint]
    [(g.modulePushforward.{z}).IsRightAdjoint] :
    ((f.comp g).modulePushforward.{z}).IsRightAdjoint :=
  modulePushforwardComp_isRightAdjoint f g

end CommRingPresentation

-- The comparison data is supplied by mathlib's sheaf-of-modules pseudofunctoriality.

end RingedSite.Hom
