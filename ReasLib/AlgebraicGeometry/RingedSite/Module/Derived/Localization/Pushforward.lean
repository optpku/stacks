/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import ReasLib.AlgebraicGeometry.RingedSite.Localization.Morphism
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pushforward.Composition
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Composition
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

-- Local instance justification (proof-local temporary data): the localized-complex and mapDerivedCategory comparisons below need both exactness proofs for the fixed localizedRestriction functor; install the named finite-limit and finite-colimit proofs only in this module.
attribute [local instance] RingedSite.Hom.localizedRestriction_preservesFiniteLimits
  RingedSite.Hom.localizedRestriction_preservesFiniteColimits

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
  (f : Hom X Y) (V : Y)
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
      (((Over.forget V ⋙ f.base).sheafPushforwardContinuous RingCat.{w}
          (Y.localization V).siteTopology X.siteTopology).obj X.structureSheaf) :=
  eqToHom (sorry) ≫ (f.localization V).structureSheafMap

/-- The left underived composite is identified with the common localized pushforward. -/
noncomputable def leftIso :
    modulePushforward f ⋙ localizedRestriction Y V ≅
      SheafOfModules.pushforward (commonMap (f := f) (V := V)) :=
  SheafOfModules.pushforwardComp (𝟙 (Y.structureSheaf.over V)) f.structureSheafMap ≪≫
    eqToIso (sorry)

/-- The right underived composite is identified with the common localized pushforward. -/
noncomputable def rightIso :
    localizedRestriction X (f.base.obj V) ⋙ modulePushforward (f.localization V) ≅
      SheafOfModules.pushforward (commonMap (f := f) (V := V)) :=
  SheafOfModules.pushforwardComp (f.localization V).structureSheafMap
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

/-- The source functor is equipped with its canonical right-derived-functor witness. -/
@[stacks 0D6G "localized source right-derived model"]
noncomputable instance source_isRightDerived :
    (source f V).IsRightDerivedFunctor (sourceUnit f V) (ModuleQis.{z} X) := sorry

/-- The target functor is equipped with its canonical right-derived-functor witness. -/
@[stacks 0D6G "localized target right-derived model"]
noncomputable instance target_isRightDerived :
    (target f V).IsRightDerivedFunctor (targetUnit f V) (ModuleQis.{z} X) := sorry

/-- Lemma 21.20.4 (0D6G): the derived localization comparison is an isomorphism of functors. -/
@[stacks 0D6G]
noncomputable def iso : source f V ≅ target f V :=
  Functor.rightDerivedNatIso (source f V) (target f V)
    (sourceUnit f V) (targetUnit f V) (ModuleQis.{z} X) (homotopyIso f V)

/-- The component of the derived localization comparison at a derived module. -/
@[stacks 0D6G "localized comparison component"]
noncomputable abbrev appIso (E : ModuleDerived.{z} X) :
    (source f V).obj E ≅ (target f V).obj E :=
  (iso f V).app E

end LocalizedPushforward

end RingedSite.Hom

-- The deferred axioms occur only in the localization equalities and derived universal-property
-- fields; the functor and comparison data are assembled by the canonical constructors above.
