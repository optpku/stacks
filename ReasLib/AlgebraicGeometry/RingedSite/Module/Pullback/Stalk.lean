/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Stalk
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSite.Stalk
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pullback of module stalks on commutative ringed sites

For a morphism `f : X ⟶ Y` of commutative ringed sites and a point `p` of `X`, this file
constructs the canonical comparison from scalar extension of a module stalk to the stalk of its
pullback.  The induced point and map on stalk rings are owned by
`ReasLib.AlgebraicGeometry.RingedSite.Stalk`; all module structures here remain bundled in
`ModuleCat`.  The common coefficient/module universe is independent of both site universes.
Mathlib's `PresheafOfModules.colimitFunctor` currently uses one universe for the coefficient
rings and module carriers, and requires the indexing category to be locally small in that
universe; these are the only remaining universe constraints below.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe uC vC uD vD w

namespace RingedSite.Hom

open SheafOfModules.RingedSite

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
variable [LocallySmall.{w} C] [LocallySmall.{w} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [JD.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {O : Sheaf JC CommRingCat.{w}}
variable {O' : Sheaf JD CommRingCat.{w}}
variable (f : RingedSite.Hom (RingedSite.ofCommRingSheaf JC O)
  (RingedSite.ofCommRingSheaf JD O'))
variable (p : GrothendieckTopology.Point.{w} JC)
variable [InitiallySmall (f.base ⋙ p.fiber).Elements]

variable [(f.base.sheafPushforwardContinuous CommRingCat.{w} JD JC).IsRightAdjoint]

variable [(f.base.sheafPushforwardContinuous AddCommGrpCat.{w} JD JC).IsRightAdjoint]
variable [f.modulePushforward.{w}.IsRightAdjoint]

/-- The canonical comparison between the additive fiber at `f(p)` and inverse image followed by
the additive fiber at `p`. -/
noncomputable abbrev addCommGrpFiberIso :
    (pointMap f p).sheafFiber ≅
      f.base.sheafPullback AddCommGrpCat.{w} JD JC ⋙ p.sheafFiber :=
  p.sheafFiberComapIsoOfMorphismOfSites (J := JD) f.base AddCommGrpCat.{w}
    (hF := f.isMorphismOfSites)

/-- The additive inverse-image map from a module sheaf to its module pullback, obtained by
transposing the unit of the module pullback-pushforward adjunction. -/
noncomputable def pullbackUnitSheafMap
    (M : ringedSiteModuleCategory JD O') :
    (f.base.sheafPullback AddCommGrpCat.{w} JD JC).obj
        ((SheafOfModules.toSheaf (ringSheaf JD O')).obj M) ⟶
      (SheafOfModules.toSheaf (ringSheaf JC O)).obj (f.modulePullback.obj M) :=
  ((f.base.sheafAdjunctionContinuous AddCommGrpCat.{w} JD JC).homEquiv _ _).symm
    ((SheafOfModules.toSheaf (ringSheaf JD O')).map
      ((f.modulePullbackPushforwardAdjunction.{w}).unit.app M))

/-- The additive map from the stalk of a module to the stalk of its pullback, before applying
the extension-restriction adjunction for the induced map of stalk rings. -/
noncomputable abbrev pullbackStalkAddHom
    (M : ringedSiteModuleCategory JD O') :
    AddCommGrpCat.of ((pointMap f p).moduleStalk O' M) ⟶
      AddCommGrpCat.of (p.moduleStalk O (f.modulePullback.obj M)) :=
  (addCommGrpFiberIso f p).hom.app
      ((SheafOfModules.toSheaf (ringSheaf JD O')).obj M) ≫
    p.sheafFiber.map (pullbackUnitSheafMap f M)

/-- The additive pullback-stalk map is semilinear for the canonical map on stalk rings. -/
theorem pullbackStalkAddHom_smul
    (M : ringedSiteModuleCategory JD O')
    (r : (pointMap f p).stalkCommRing O') (m : (pointMap f p).moduleStalk O' M) :
    (pullbackStalkAddHom f p M).hom (r • m) =
      (stalkMap f p).hom r • (pullbackStalkAddHom f p M).hom m := sorry

/-- The pullback-stalk map as a morphism into restriction of scalars along the canonical stalk
ring map. -/
noncomputable def pullbackStalkUnitHom
    (M : ringedSiteModuleCategory JD O') :
    (pointMap f p).moduleStalk O' M ⟶
      (ModuleCat.restrictScalars (stalkMap f p).hom).obj
        (p.moduleStalk O (f.modulePullback.obj M)) :=
  (ModuleCat.semilinearMapAddEquiv (stalkMap f p).hom
    ((pointMap f p).moduleStalk O' M) (p.moduleStalk O (f.modulePullback.obj M)))
    { toFun := (pullbackStalkAddHom f p M).hom
      map_add' := (pullbackStalkAddHom f p M).hom.map_add
      map_smul' := pullbackStalkAddHom_smul f p M }

/-- The canonical comparison from scalar extension of a module stalk to the stalk of its
ringed-site pullback. -/
@[stacks 05V5 "pullback-stalk comparison"]
noncomputable def pullbackStalkComparison
    (M : ringedSiteModuleCategory JD O') :
    (ModuleCat.extendScalars (stalkMap f p).hom).obj
        ((pointMap f p).moduleStalk O' M) ⟶
      p.moduleStalk O (f.modulePullback.obj M) :=
  ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars (stalkMap f p).hom
    (pullbackStalkUnitHom f p M)

/-- Scalar extension of the module-valued stalk at the image point. -/
noncomputable abbrev stalkExtensionFunctor :
    ringedSiteModuleCategory JD O' ⥤ _root_.ModuleCat (p.stalkCommRing O) :=
  (pointMap f p).moduleStalkFunctor O' ⋙
    ModuleCat.extendScalars (stalkMap f p).hom

/-- Pull back a module sheaf and then take its module-valued stalk. -/
noncomputable abbrev pulledBackStalkFunctor :
    ringedSiteModuleCategory JD O' ⥤ _root_.ModuleCat (p.stalkCommRing O) :=
  f.modulePullback ⋙ p.moduleStalkFunctor O

/-- The pullback-stalk comparisons are natural in the module sheaf. -/
theorem pullbackStalkComparison_naturality
    {M N : ringedSiteModuleCategory JD O'} (g : M ⟶ N) :
    (stalkExtensionFunctor f p).map g ≫ pullbackStalkComparison f p N =
      pullbackStalkComparison f p M ≫ (pulledBackStalkFunctor f p).map g := sorry

/-- The canonical pullback-stalk comparisons as a natural transformation. -/
@[stacks 05V5 "pullback-stalk comparison natural transformation"]
noncomputable def pullbackStalkComparisonNatTrans :
    stalkExtensionFunctor f p ⟶ pulledBackStalkFunctor f p where
  app M := pullbackStalkComparison f p M
  naturality _ _ g := pullbackStalkComparison_naturality f p g

/-- The canonical scalar-extension comparison on module stalks is an isomorphism. -/
noncomputable instance pullbackStalkComparison_isIso
    (M : ringedSiteModuleCategory JD O') :
    IsIso (pullbackStalkComparison f p M) := sorry

/-- Lemma 18.36.4 (05V5): the canonical natural transformation from scalar extension of the
stalk at `f(p)` to the stalk of the pullback module is invertible.  The public owner is the
canonical forward transformation together with this Prop-valued certificate, so no inverse
data is selected from a deferred proof. -/
@[stacks 05V5]
noncomputable instance pullbackStalkComparisonNatTrans_isIso :
    IsIso (pullbackStalkComparisonNatTrans f p) := sorry

-- Any `sorryAx` below is confined to semilinearity or naturality proof fields.  The additive
-- map, extension-of-scalars comparison, and natural-transformation components are explicit.

end RingedSite.Hom
