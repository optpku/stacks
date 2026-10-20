module

public import Mathlib.CategoryTheory.Comma.LocallySmall
public import ReasLib.AlgebraicGeometry.RingedSite.Localization
public import ReasLib.CategoryTheory.Sites.Over.MorphismOfSites
public import ReasLib.CategoryTheory.Sites.Over.Pushforward
import Mathlib.Tactic.CrossRefAttribute

/-!
# Morphisms between localized ringed sites

This module owns the morphism on slice ringed sites induced by a morphism of ringed sites.  The
base functor, the structure-sheaf map, and their comparison API live here so later constructions
can use localization without importing a chapter facade.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe uX vX uY vY t w z

namespace RingedSite.Hom

variable {X : RingedSite.{uX, vX, t}} {Y : RingedSite.{uY, vY, t}}

/-- The functor induced on slice categories by a morphism of ringed sites is a morphism of sites. -/
@[stacks 04J0 "(base site)"]
theorem localization_base_isMorphismOfSites (f : X.Hom Y) (V : Y.carrier) :
    IsMorphismOfSites (Y.siteTopology.over V)
      (X.siteTopology.over (f.base.obj V)) (Over.post f.base) := sorry

/-- The structure-sheaf map of the localized morphism induced by `f` at `V`. -/
@[stacks 04J0 "(structure map)"]
noncomputable def localizationStructureSheafMap (f : X.Hom Y) (V : Y.carrier) :
    Y.structureSheaf.over V ⟶
      (@Functor.sheafPushforwardOverPost _ _ _ _ X.siteTopology Y.siteTopology
        f.base f.base_isContinuous V RingCat.{t} _).obj
        (X.structureSheaf.over (f.base.obj V)) :=
  (Y.siteTopology.overPullback RingCat.{t} V).map f.structureSheafMap ≫
    ((@Functor.sheafPushforwardOverPostComp _ _ _ _ X.siteTopology Y.siteTopology
      f.base f.base_isContinuous V RingCat.{t} _).symm.app
      X.structureSheaf).hom

/-- A morphism of ringed sites induces a morphism between the
localizations at `V` and `f.base.obj V`. -/
@[stacks 04J0]
noncomputable def localization (f : X.Hom Y) (V : Y.carrier) :
    (X.localization (f.base.obj V)).Hom (Y.localization V) where
  base := Over.post f.base
  isMorphismOfSites := localization_base_isMorphismOfSites f V
  structureSheafMap := localizationStructureSheafMap f V

/-- The base functor of `localization f V` is continuous. -/
theorem localization_isContinuous (f : X.Hom Y) (V : Y.carrier) :
    (localization f V).base.IsContinuous (Y.siteTopology.over V)
      (X.siteTopology.over (f.base.obj V)) := sorry

/-- The inverse-image functor of `localization f V` preserves finite limits whenever the
corresponding slice-site inverse image does. -/
theorem localization_sheafPullback_preservesFiniteLimits
    (f : X.Hom Y) (V : Y.carrier) [UnivLE.{max uX vX, t}]
    [UnivLE.{max uY vY vX, t}]
    [PreservesFiniteLimits
      (@Functor.sheafPullback _ _ _ _ (Over.post f.base) (Type t) _
        (Y.siteTopology.over V) (X.siteTopology.over (f.base.obj V))
        (@Functor.IsContinuous.overPost _ _ _ _ f.base Y.siteTopology X.siteTopology
          f.base_isContinuous V) inferInstance)] :
    PreservesFiniteLimits
      (@Functor.sheafPullback _ _ _ _ (localization f V).base (Type t) _
        (Y.siteTopology.over V) (X.siteTopology.over (f.base.obj V))
        (localization_isContinuous f V) inferInstance) := sorry

/-- The base functor of the localized morphism is `Over.post f.base`. -/
@[stacks 04J0 "(base)"]
theorem localization_base (f : X.Hom Y) (V : Y.carrier) :
    (localization f V).base = Over.post f.base := sorry

/-- The structure-sheaf map of the localized morphism is restriction of
`f.structureSheafMap`, transported through the slice pushforward comparison. -/
@[stacks 04J0 "(structure map formula)", stacks 04J7 "structure map"]
theorem localization_structureSheafMap_eq (f : X.Hom Y) (V : Y.carrier) :
    (localization f V).structureSheafMap = localizationStructureSheafMap f V := sorry

/-- Direct image commutes with restriction to the slice, giving the underlying localized
topos square. -/
@[stacks 04J0 "(topos square)", stacks 04J7 "topos square"]
noncomputable def localizationPushforwardIso (f : X.Hom Y) (V : Y.carrier)
    (A : Type w) [Category.{z} A] :
    X.siteTopology.overPullback A (f.base.obj V) ⋙
        @Functor.sheafPushforwardOverPost _ _ _ _ X.siteTopology Y.siteTopology
          f.base f.base_isContinuous V A _ ≅
      @Functor.sheafPushforwardContinuous _ _ _ _ f.base A _
        Y.siteTopology X.siteTopology f.base_isContinuous ⋙
        Y.siteTopology.overPullback A V :=
  @Functor.sheafPushforwardOverPostComp _ _ _ _ X.siteTopology Y.siteTopology
    f.base f.base_isContinuous V A _

end RingedSite.Hom
