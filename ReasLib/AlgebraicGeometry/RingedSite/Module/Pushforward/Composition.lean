/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

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
theorem modulePushforwardComp_isRightAdjoint.{z, uX, vX, uY, vY, uZ, vZ, w}
    {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
    {Z : RingedSite.{uZ, vZ, w}} (f : Hom X Y) (g : Hom Y Z)
    [(f.modulePushforward.{z}).IsRightAdjoint]
    [(g.modulePushforward.{z}).IsRightAdjoint] :
    ((Hom.comp f g).modulePushforward.{z}).IsRightAdjoint :=
  Functor.isRightAdjoint_of_iso (modulePushforwardCompIso f g)

namespace CommRingPresentation

/-- A composite module pushforward between sites presented by commutative ring sheaves is
a right adjoint whenever both constituent pushforwards are right adjoints. -/
@[stacks 03D8 "commutative presentation right adjoint composition"]
theorem modulePushforwardCompIsRightAdjoint.{z, uX, vX, uY, vY, uZ, vZ, w}
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
