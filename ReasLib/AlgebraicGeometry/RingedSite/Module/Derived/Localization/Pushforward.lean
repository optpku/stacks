module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import ReasLib.AlgebraicGeometry.RingedSite.Localization.Morphism
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pushforward.Composition
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Composition
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

-- This is the standard quotient used by the named ringed-site models.
-- Local instance justification (defeq pin): the imported ModuleDerived and localized ModuleCat aliases use the standard homotopy localization; this fallback is definitionally the same quotient as the named moduleCat_hasDerivedCategory and does not choose another derived model.
attribute [local instance] HasDerivedCategory.standard

-- Keep these operations on the already specified canonical derived-category model.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory

/-!
# Derived pushforward and localization

This file owns the reusable Beck--Chevalley comparison for a ringed-site morphism after
localizing at an object.  The namespace keeps the source-facing names short while the
underived, homotopy, and derived layers remain separate.
-/

open CategoryTheory CategoryTheory.Limits
-- Local instance justification (defeq pin): the generic ringed-site ModuleCat derived owner is
-- required by the derived-category APIs in this presentation.
-- Local instance justification (defeq pin): ModuleDerived and DerivedCategory.Q must elaborate to the same bundled-ringed-site standard localization; enable the existing reducible moduleCat_hasDerivedCategory owner only for these module comparisons.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory
open ComplexShape

noncomputable section

universe z uX vX uY vY w

namespace RingedSite.Hom

namespace LocalizedPushforward

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
  (f : Hom X Y) (V : Y.carrier)
variable [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]
variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived.{z} f) (ModuleQis.{z} X)]
variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived.{z} (f.localization V))
  (ModuleQis.{z} (X.localization (f.base.obj V)))]

/- The normalized map is kept as concrete data so all later functors share one ring map owner. -/

/-- The structure-sheaf map in the common normal form for localization at `V`. -/
@[stacks 0D6G "localized structure-sheaf map"]
noncomputable def commonMap :
    (Y.localization V).structureSheaf ⟶
      ((@Functor.sheafPushforwardContinuous _ _ _ _ (Over.forget V ⋙ f.base)
          RingCat.{w} _ (Y.localization V).siteTopology X.siteTopology
          (@Functor.IsContinuous.overForgetComp _ _ _ _ f.base
            Y.siteTopology X.siteTopology f.base_isContinuous V)).obj X.structureSheaf) :=
  eqToHom (sorry) ≫ (f.localization V).structureSheafMap

/-- The left underived composite is identified with the common localized pushforward. -/
noncomputable def leftIso :
    modulePushforward f ⋙ localizedRestriction Y V ≅
      @SheafOfModules.pushforward _ _ _ _
        (Y.localization V).siteTopology X.siteTopology (Over.forget V ⋙ f.base)
        (Y.localization V).structureSheaf X.structureSheaf
        (@Functor.IsContinuous.overForgetComp _ _ _ _ f.base
          Y.siteTopology X.siteTopology f.base_isContinuous V)
        (commonMap (f := f) (V := V)) :=
  @SheafOfModules.pushforwardComp _ _ _ _ _ _
    (Y.localization V).siteTopology Y.siteTopology (Over.forget V)
    (Y.localization V).structureSheaf Y.structureSheaf inferInstance
    (𝟙 (Y.structureSheaf.over V)) X.siteTopology f.base X.structureSheaf
    f.base_isContinuous f.structureSheafMap ≪≫
    eqToIso (sorry)

/-- The right underived composite is identified with the common localized pushforward. -/
noncomputable def rightIso :
    localizedRestriction X (f.base.obj V) ⋙ modulePushforward (f.localization V) ≅
      @SheafOfModules.pushforward _ _ _ _
        (Y.localization V).siteTopology X.siteTopology (Over.forget V ⋙ f.base)
        (Y.localization V).structureSheaf X.structureSheaf
        (@Functor.IsContinuous.overForgetComp _ _ _ _ f.base
          Y.siteTopology X.siteTopology f.base_isContinuous V)
        (commonMap (f := f) (V := V)) :=
  @SheafOfModules.pushforwardComp _ _ _ _ _ _
    (Y.localization V).siteTopology (X.localization (f.base.obj V)).siteTopology
    (f.localization V).base (Y.localization V).structureSheaf
    (X.localization (f.base.obj V)).structureSheaf
    (f.localization V).base_isContinuous (f.localization V).structureSheafMap
    X.siteTopology (Over.forget (f.base.obj V)) X.structureSheaf inferInstance
    (𝟙 (X.structureSheaf.over (f.base.obj V))) ≪≫
    eqToIso (sorry)

/-- The underived localization comparison, in the direction used by derived functors. -/
@[stacks 0D6G "underived localization comparison"]
noncomputable abbrev underivedIso :
    modulePushforward f ⋙ localizedRestriction Y V ≅
      localizedRestriction X (f.base.obj V) ⋙ modulePushforward (f.localization V) :=
  leftIso f V ≪≫ (rightIso f V).symm

/-- The homotopy-level source functor for the localized pushforward comparison. -/
noncomputable abbrev homotopySource :
    ModuleHomotopy.{z} X ⥤ ModuleDerived.{z} (Y.localization V) :=
  modulePushforwardToDerived.{z} f ⋙ localizedRestrictionDerived.{z} Y V

/-- The homotopy-level target functor for the localized pushforward comparison. -/
noncomputable abbrev homotopyTarget :
    ModuleHomotopy.{z} X ⥤ ModuleDerived.{z} (Y.localization V) :=
  (localizedRestriction.{z} X (f.base.obj V)).mapHomotopyCategory (up ℤ) ⋙
    modulePushforwardToDerived.{z} (f.localization V)

/-- The derived source functor `R f_*` followed by restriction to `Y/V`. -/
noncomputable abbrev source :
    ModuleDerived.{z} X ⥤ ModuleDerived.{z} (Y.localization V) :=
  modulePushforwardDerived.{z} f ⋙ localizedRestrictionDerived.{z} Y V

/-- The derived target functor obtained by first restricting to `X/f(V)` and then pushing forward. -/
noncomputable abbrev target :
    ModuleDerived.{z} X ⥤ ModuleDerived.{z} (Y.localization V) :=
  localizedRestrictionDerived.{z} X (f.base.obj V) ⋙
    modulePushforwardDerived.{z} (f.localization V)

/-- The homotopy-level Beck--Chevalley isomorphism induced by `underivedIso`. -/
noncomputable def homotopyIso : homotopySource f V ≅ homotopyTarget f V :=
  (Functor.associator
    ((modulePushforward.{z} f).mapHomotopyCategory (up ℤ))
    (moduleLocalization.{z} Y)
    (localizedRestrictionDerived.{z} Y V)).symm ≪≫
  Functor.isoWhiskerLeft
    ((modulePushforward.{z} f).mapHomotopyCategory (up ℤ))
    (localizedRestriction.{z} Y V).mapDerivedCategoryFactorsh ≪≫
  Functor.associator
    ((modulePushforward.{z} f).mapHomotopyCategory (up ℤ))
    ((localizedRestriction.{z} Y V).mapHomotopyCategory (up ℤ))
    (moduleLocalization.{z} (Y.localization V)) ≪≫
  Functor.isoWhiskerRight
    (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (modulePushforward.{z} f ⋙ localizedRestriction.{z} Y V)) (up ℤ))
    (moduleLocalization.{z} (Y.localization V)) ≪≫
  Functor.isoWhiskerRight
    (Functor.mapHomotopyCategoryIso (underivedIso f V))
    (moduleLocalization.{z} (Y.localization V)) ≪≫
  Functor.isoWhiskerRight
    ((Functor.mapHomotopyCategoryCompIso
      (Iso.refl
        (localizedRestriction.{z} X (f.base.obj V) ⋙
          modulePushforward.{z} (f.localization V))) (up ℤ)).symm)
    (moduleLocalization.{z} (Y.localization V)) ≪≫
  (Functor.associator
    ((localizedRestriction.{z} X (f.base.obj V)).mapHomotopyCategory (up ℤ))
    ((modulePushforward.{z} (f.localization V)).mapHomotopyCategory (up ℤ))
    (moduleLocalization.{z} (Y.localization V))).symm

/-- The canonical right-derived unit on the source side. -/
noncomputable def sourceUnit :
    homotopySource f V ⟶ moduleLocalization.{z} X ⋙ source f V :=
  Functor.whiskerRight
      (Functor.totalRightDerivedUnit
        (modulePushforwardToDerived.{z} f)
        (moduleLocalization.{z} X) (ModuleQis.{z} X))
      (localizedRestrictionDerived.{z} Y V) ≫
    (Functor.associator
      (moduleLocalization.{z} X)
      (modulePushforwardDerived.{z} f)
      (localizedRestrictionDerived.{z} Y V)).hom

/-- The canonical right-derived unit on the localized target side. -/
noncomputable def targetUnit :
    homotopyTarget f V ⟶ moduleLocalization.{z} X ⋙ target f V :=
  Functor.whiskerLeft
      ((localizedRestriction.{z} X (f.base.obj V)).mapHomotopyCategory (up ℤ))
      (Functor.totalRightDerivedUnit
        (modulePushforwardToDerived.{z} (f.localization V))
        (moduleLocalization.{z} (X.localization (f.base.obj V)))
        (ModuleQis.{z} (X.localization (f.base.obj V)))) ≫
    (Functor.associator
      ((localizedRestriction.{z} X (f.base.obj V)).mapHomotopyCategory (up ℤ))
      (moduleLocalization.{z} (X.localization (f.base.obj V)))
      (modulePushforwardDerived.{z} (f.localization V))).inv ≫
    Functor.whiskerRight
      (localizedRestriction.{z} X (f.base.obj V)).mapDerivedCategoryFactorsh.inv
      (modulePushforwardDerived.{z} (f.localization V)) ≫
    (Functor.associator
      (moduleLocalization.{z} X)
      (localizedRestrictionDerived.{z} X (f.base.obj V))
      (modulePushforwardDerived.{z} (f.localization V))).hom

/- The source and target right-derived laws are caller-supplied below.  Keeping them explicit is
   essential: `rightDerivedNatIso` descends both maps from the supplied universal-property
   witnesses, so a global admitted instance would silently choose the inverse data as well. -/

/-- The derived localization comparison is an isomorphism of functors,
given the right-derived universal properties for the two specified units. -/
@[stacks 0D6G]
noncomputable def iso
    [source_isRightDerived :
      (source f V).IsRightDerivedFunctor (sourceUnit f V) (ModuleQis.{z} X)]
    [target_isRightDerived :
      (target f V).IsRightDerivedFunctor (targetUnit f V) (ModuleQis.{z} X)] :
    source f V ≅ target f V :=
  Functor.rightDerivedNatIso (source f V) (target f V)
    (sourceUnit f V) (targetUnit f V) (ModuleQis.{z} X) (homotopyIso f V)

/-- The component of the derived localization comparison at a derived module. -/
@[stacks 0D6G "localized comparison component"]
noncomputable abbrev appIso (E : ModuleDerived.{z} X)
    [source_isRightDerived :
      (source f V).IsRightDerivedFunctor (sourceUnit f V) (ModuleQis.{z} X)]
    [target_isRightDerived :
      (target f V).IsRightDerivedFunctor (targetUnit f V) (ModuleQis.{z} X)] :
    (source f V).obj E ≅ (target f V).obj E :=
  (iso f V).app E

end LocalizedPushforward

end RingedSite.Hom

-- The remaining local proof debt consists of the localization equalities. The derived comparison
-- consumes the right-derived universal-property witnesses supplied by its caller.
