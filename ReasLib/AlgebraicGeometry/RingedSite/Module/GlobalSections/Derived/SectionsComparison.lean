/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived.Naturality
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Objectwise
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Exact
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Induced.Preadditive
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived sections over an object and direct image

This file owns the objectwise form of the global-sections/direct-image comparison. The
restriction-of-scalars functor is named here so all comparisons use the same ring map.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open ComplexShape

noncomputable section

universe z uX vX uY vY w

namespace RingedSite.Hom

-- Local instance justification (defeq pin): generic derived-section comparison APIs must align with the canonical RingedSite.Hom.ModuleDerived presentation.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable [UnivLE.{uX, w}] [UnivLE.{uY, w}]
variable [UnivLE.{max uX vX, w}] [UnivLE.{max uY vY, w}]
variable [UnivLE.{max uY vX, w}]

/-- The derived restriction of scalars on modules of sections at an object. -/
@[stacks 0D6H "derived section-ring restriction"]
noncomputable abbrev sectionsRestrictionDerived.{z₁, u₁, v₁, u₂, v₂, w₁}
    {X : RingedSite.{u₁, v₁, w₁}} {Y : RingedSite.{u₂, v₂, w₁}}
    [UnivLE.{u₁, w₁}] [UnivLE.{u₂, w₁}]
    [UnivLE.{max u₁ v₁, w₁}] [UnivLE.{max u₂ v₂, w₁}]
    (f : X.Hom Y) (V : Y)
    [UnivLE.{max u₁ v₁, z₁}] [UnivLE.{max u₂ v₂, z₁}] :
    ModuleSections.DerivedAt.{z₁} X (f.base.obj V) ⥤
      ModuleSections.DerivedAt.{z₁} Y V :=
  @CategoryTheory.Functor.mapDerivedCategory
    (_root_.ModuleCat.{z₁} (X.structureSheaf.obj.obj (op (f.base.obj V))))
    inferInstance inferInstance
    (ModuleCat.hasDerivedCategory (X.structureSheaf.obj.obj (op (f.base.obj V))))
    (_root_.ModuleCat.{z₁} (Y.structureSheaf.obj.obj (op V)))
    inferInstance inferInstance
    (ModuleCat.hasDerivedCategory (Y.structureSheaf.obj.obj (op V)))
    (sectionsRestriction.{z₁, u₁, v₁, u₂, v₂, w₁} f V)
    inferInstance inferInstance inferInstance

namespace ModuleSections

variable [UnivLE.{uX, z}] [UnivLE.{uY, z}]

/-- The homotopy-level source for objectwise direct-image comparison. -/
@[stacks 0D6H "objectwise sections source"]
noncomputable abbrev objectSource (f : X.Hom Y) (V : Y)
    [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}] :
    ModuleHomotopy.{z} X ⥤ ModuleSections.DerivedAt.{z} Y V :=
  moduleSectionsToDerived.{z} X (f.base.obj V) ⋙ sectionsRestrictionDerived f V

/-- The homotopy-level target for objectwise direct-image comparison. -/
@[stacks 0D6H "objectwise sections target"]
noncomputable abbrev objectTarget (f : X.Hom Y) (V : Y) :
    ModuleHomotopy.{z} X ⥤ ModuleSections.DerivedAt.{z} Y V :=
  f.modulePushforward.{z}.mapHomotopyCategory (up ℤ) ⋙
    moduleSectionsToDerived.{z} Y V

/-- The source right-derived functor for sections over `f⁻¹(V)`, followed by restriction of
scalars. -/
@[stacks 0D6H "derived objectwise sections source"]
noncomputable abbrev objectSourceDerived (f : X.Hom Y) (V : Y)
    [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]
    [IsGrothendieckAbelian (ModuleCat.{z} X)] :
    ModuleDerived.{z} X ⥤ ModuleSections.DerivedAt.{z} Y V :=
  moduleSectionsDerived.{z} X (f.base.obj V) ⋙ sectionsRestrictionDerived f V

/-- The target right-derived functor for direct image followed by sections over `V`. -/
@[stacks 0D6H "derived objectwise sections target"]
noncomputable abbrev objectTargetDerived (f : X.Hom Y) (V : Y)
    [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]
    [IsGrothendieckAbelian (ModuleCat.{z} X)]
    [IsGrothendieckAbelian (ModuleCat.{z} Y)] :
    ModuleDerived.{z} X ⥤ ModuleSections.DerivedAt.{z} Y V :=
  (@modulePushforwardDerived.{z} X Y f inferInstance inferInstance
      (modulePushforwardToDerived.hasRightDerived f)) ⋙
    moduleSectionsDerived.{z} Y V

/-- The canonical unit for the source right-derived objectwise sections functor. -/
noncomputable def objectSourceUnit (f : X.Hom Y) (V : Y)
    [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]
    [IsGrothendieckAbelian (ModuleCat.{z} X)] :
    objectSource f V ⟶
      moduleLocalization.{z} X ⋙ objectSourceDerived f V :=
  Functor.whiskerRight
      (@Functor.totalRightDerivedUnit
        (ModuleHomotopy.{z} X) (ModuleDerived.{z} X)
        (ModuleSections.DerivedAt.{z} X (f.base.obj V))
        inferInstance inferInstance inferInstance
        (moduleSectionsToDerived.{z} X (f.base.obj V)) (moduleLocalization.{z} X)
        (ModuleQis.{z} X) inferInstance
        (moduleSectionsToDerived_hasRightDerivedFunctor X (f.base.obj V)))
      (sectionsRestrictionDerived f V) ≫
    (Functor.associator
      (moduleLocalization.{z} X)
      (moduleSectionsDerived.{z} X (f.base.obj V))
      (sectionsRestrictionDerived f V)).hom

/-- The canonical unit for the target right-derived objectwise sections functor. -/
noncomputable def objectTargetUnit (f : X.Hom Y) (V : Y)
    [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]
    [IsGrothendieckAbelian (ModuleCat.{z} X)]
    [IsGrothendieckAbelian (ModuleCat.{z} Y)] :
    objectTarget f V ⟶
      moduleLocalization.{z} X ⋙ objectTargetDerived f V :=
  Functor.whiskerLeft
      (f.modulePushforward.{z}.mapHomotopyCategory (up ℤ))
      (@Functor.totalRightDerivedUnit
        (ModuleHomotopy.{z} Y) (ModuleDerived.{z} Y)
        (ModuleSections.DerivedAt.{z} Y V)
        inferInstance inferInstance inferInstance
        (moduleSectionsToDerived.{z} Y V) (moduleLocalization.{z} Y)
        (ModuleQis.{z} Y) inferInstance
        (moduleSectionsToDerived_hasRightDerivedFunctor Y V)) ≫
    (Functor.associator
      (f.modulePushforward.{z}.mapHomotopyCategory (up ℤ))
      (moduleLocalization.{z} Y)
      (moduleSectionsDerived.{z} Y V)).hom ≫
    Functor.whiskerRight
      (@Functor.totalRightDerivedUnit
        (ModuleHomotopy.{z} X) (ModuleDerived.{z} X) (ModuleDerived.{z} Y)
        inferInstance inferInstance inferInstance
        (modulePushforwardToDerived.{z} f)
        (moduleLocalization.{z} X) (ModuleQis.{z} X) inferInstance
        (modulePushforwardToDerived.hasRightDerived f))
      (moduleSectionsDerived.{z} Y V) ≫
    (Functor.associator
      (moduleLocalization.{z} X)
      (@modulePushforwardDerived.{z} X Y f inferInstance inferInstance
        (modulePushforwardToDerived.hasRightDerived f))
      (moduleSectionsDerived.{z} Y V)).hom

/- The following transformation transports the underived map through homotopy categories and
the canonical factorization of an exact functor through the derived category. -/

/-- The homotopy-to-derived objectwise comparison with the canonical source model. -/
@[stacks 0D6H "derived objectwise sections naturality"]
noncomputable def objectPushforwardDerivedNat (f : X.Hom Y) (V : Y)
    [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}] :
  objectSource f V ⟶ objectTarget f V :=
  (Functor.associator
      (@Functor.mapHomotopyCategory ℤ (ModuleCat.{z} X) inferInstance inferInstance
        (_root_.ModuleCat.{z} (X.structureSheaf.obj.obj (op (f.base.obj V))))
        inferInstance inferInstance (objectFunctor.{z} X (f.base.obj V))
        (moduleSectionsEvaluation_additive X (f.base.obj V)) (up ℤ))
      (@DerivedCategory.Qh
        (_root_.ModuleCat.{z} (X.structureSheaf.obj.obj (op (f.base.obj V))))
        inferInstance inferInstance
        (ModuleCat.hasDerivedCategory (X.structureSheaf.obj.obj (op (f.base.obj V)))))
      (sectionsRestrictionDerived f V)).hom ≫
    Functor.whiskerLeft
      (@Functor.mapHomotopyCategory ℤ (ModuleCat.{z} X) inferInstance inferInstance
        (_root_.ModuleCat.{z} (X.structureSheaf.obj.obj (op (f.base.obj V))))
        inferInstance inferInstance (objectFunctor.{z} X (f.base.obj V))
        (moduleSectionsEvaluation_additive X (f.base.obj V)) (up ℤ))
      ((@Functor.mapDerivedCategoryFactorsh
        (_root_.ModuleCat.{z} (X.structureSheaf.obj.obj (op (f.base.obj V))))
        inferInstance inferInstance
        (ModuleCat.hasDerivedCategory (X.structureSheaf.obj.obj (op (f.base.obj V))))
        (_root_.ModuleCat.{z} (Y.structureSheaf.obj.obj (op V)))
        inferInstance inferInstance
        (ModuleCat.hasDerivedCategory (Y.structureSheaf.obj.obj (op V)))
        (sectionsRestriction f V) inferInstance inferInstance inferInstance).hom) ≫
    (Functor.associator
      (@Functor.mapHomotopyCategory ℤ (ModuleCat.{z} X) inferInstance inferInstance
        (_root_.ModuleCat.{z} (X.structureSheaf.obj.obj (op (f.base.obj V))))
        inferInstance inferInstance (objectFunctor.{z} X (f.base.obj V))
        (moduleSectionsEvaluation_additive X (f.base.obj V)) (up ℤ))
      (@Functor.mapHomotopyCategory ℤ
        (_root_.ModuleCat.{z} (X.structureSheaf.obj.obj (op (f.base.obj V))))
        inferInstance inferInstance
        (_root_.ModuleCat.{z} (Y.structureSheaf.obj.obj (op V)))
        inferInstance inferInstance (sectionsRestriction f V) inferInstance (up ℤ))
      (@DerivedCategory.Qh (_root_.ModuleCat.{z} (Y.structureSheaf.obj.obj (op V)))
        inferInstance inferInstance
        (ModuleCat.hasDerivedCategory (Y.structureSheaf.obj.obj (op V))))).inv ≫
    Functor.whiskerRight
      ((@Functor.mapHomotopyCategoryCompIso ℤ
        (ModuleCat.{z} X) inferInstance inferInstance
        (_root_.ModuleCat.{z} (X.structureSheaf.obj.obj (op (f.base.obj V))))
        inferInstance inferInstance
        (_root_.ModuleCat.{z} (Y.structureSheaf.obj.obj (op V)))
        inferInstance inferInstance
        (objectFunctor.{z} X (f.base.obj V)) (sectionsRestriction f V)
        (objectFunctor.{z} X (f.base.obj V) ⋙ sectionsRestriction f V)
        (Iso.refl _) (moduleSectionsEvaluation_additive X (f.base.obj V)) inferInstance
        (@Functor.instAdditiveComp
          (ModuleCat.{z} X)
          (_root_.ModuleCat.{z} (X.structureSheaf.obj.obj (op (f.base.obj V))))
          inferInstance inferInstance inferInstance inferInstance
          (objectFunctor.{z} X (f.base.obj V))
          (moduleSectionsEvaluation_additive X (f.base.obj V))
          (_root_.ModuleCat.{z} (Y.structureSheaf.obj.obj (op V)))
          inferInstance inferInstance (sectionsRestriction f V) inferInstance)
        (up ℤ)).hom)
      (@DerivedCategory.Qh (_root_.ModuleCat.{z} (Y.structureSheaf.obj.obj (op V)))
        inferInstance inferInstance
        (ModuleCat.hasDerivedCategory (Y.structureSheaf.obj.obj (op V)))) ≫
    Functor.whiskerRight
      (@NatTrans.mapHomotopyCategory ℤ (ModuleCat.{z} X) inferInstance inferInstance
        (_root_.ModuleCat.{z} (Y.structureSheaf.obj.obj (op V)))
        inferInstance inferInstance
        (objectFunctor.{z} X (f.base.obj V) ⋙ sectionsRestriction f V)
        (f.modulePushforward.{z} ⋙ objectFunctor.{z} Y V)
        (@Functor.instAdditiveComp
          (ModuleCat.{z} X)
          (_root_.ModuleCat.{z} (X.structureSheaf.obj.obj (op (f.base.obj V))))
          inferInstance inferInstance inferInstance inferInstance
          (objectFunctor.{z} X (f.base.obj V))
          (moduleSectionsEvaluation_additive X (f.base.obj V))
          (_root_.ModuleCat.{z} (Y.structureSheaf.obj.obj (op V)))
          inferInstance inferInstance (sectionsRestriction f V) inferInstance)
        (@Functor.instAdditiveComp
          (ModuleCat.{z} X) (ModuleCat.{z} Y)
          inferInstance inferInstance inferInstance inferInstance
          f.modulePushforward inferInstance
          (_root_.ModuleCat.{z} (Y.structureSheaf.obj.obj (op V)))
          inferInstance inferInstance (objectFunctor.{z} Y V)
          (moduleSectionsEvaluation_additive Y V))
        (objectPushforwardNat f V) (up ℤ))
      (@DerivedCategory.Qh (_root_.ModuleCat.{z} (Y.structureSheaf.obj.obj (op V)))
        inferInstance inferInstance
        (ModuleCat.hasDerivedCategory (Y.structureSheaf.obj.obj (op V)))) ≫
    Functor.whiskerRight
      ((@Functor.mapHomotopyCategoryCompIso ℤ
        (ModuleCat.{z} X) inferInstance inferInstance
        (ModuleCat.{z} Y) inferInstance inferInstance
        (_root_.ModuleCat.{z} (Y.structureSheaf.obj.obj (op V)))
        inferInstance inferInstance
        f.modulePushforward (objectFunctor.{z} Y V)
        (f.modulePushforward.{z} ⋙ objectFunctor.{z} Y V)
        (Iso.refl _) inferInstance (moduleSectionsEvaluation_additive Y V)
        (@Functor.instAdditiveComp
          (ModuleCat.{z} X) (ModuleCat.{z} Y)
          inferInstance inferInstance inferInstance inferInstance
          f.modulePushforward inferInstance
          (_root_.ModuleCat.{z} (Y.structureSheaf.obj.obj (op V)))
          inferInstance inferInstance (objectFunctor.{z} Y V)
          (moduleSectionsEvaluation_additive Y V))
        (up ℤ)).inv)
      (@DerivedCategory.Qh (_root_.ModuleCat.{z} (Y.structureSheaf.obj.obj (op V)))
        inferInstance inferInstance
        (ModuleCat.hasDerivedCategory (Y.structureSheaf.obj.obj (op V)))) ≫
    (Functor.associator
      (f.modulePushforward.{z}.mapHomotopyCategory (up ℤ))
      (@Functor.mapHomotopyCategory ℤ (ModuleCat.{z} Y) inferInstance inferInstance
        (_root_.ModuleCat.{z} (Y.structureSheaf.obj.obj (op V)))
        inferInstance inferInstance (objectFunctor.{z} Y V)
        (moduleSectionsEvaluation_additive Y V) (up ℤ))
      (@DerivedCategory.Qh (_root_.ModuleCat.{z} (Y.structureSheaf.obj.obj (op V)))
        inferInstance inferInstance
        (ModuleCat.hasDerivedCategory (Y.structureSheaf.obj.obj (op V))))).hom

/-- The source objectwise functor is a right-derived model of sections followed by scalar
restriction. -/
@[stacks 0D6H "derived objectwise sections source model"]
theorem objectSource_isRightDerived
    (f : X.Hom Y) (V : Y)
    [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]
    [IsGrothendieckAbelian (ModuleCat.{z} X)] :
    (objectSourceDerived f V).IsRightDerivedFunctor
      (objectSourceUnit f V) (ModuleQis.{z} X) := sorry

/-- The target objectwise functor is a right-derived model of direct image followed by sections. -/
@[stacks 0D6H "derived objectwise sections target model"]
theorem objectTarget_isRightDerived
    (f : X.Hom Y) (V : Y)
    [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]
    [IsGrothendieckAbelian (ModuleCat.{z} X)]
    [IsGrothendieckAbelian (ModuleCat.{z} Y)] :
    (objectTargetDerived f V).IsRightDerivedFunctor
      (objectTargetUnit f V) (ModuleQis.{z} X) := sorry

/-- The canonical derived comparison for sections over `V`. -/
@[stacks 0D6H "derived objectwise sections comparison"]
noncomputable def objectPushforwardComparison (f : X.Hom Y) (V : Y)
    [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]
    [IsGrothendieckAbelian (ModuleCat.{z} X)]
    [IsGrothendieckAbelian (ModuleCat.{z} Y)] :
    objectSourceDerived f V ⟶ objectTargetDerived f V :=
  @Functor.rightDerivedNatTrans
    (ModuleHomotopy.{z} X) (ModuleDerived.{z} X) (ModuleSections.DerivedAt.{z} Y V)
    inferInstance inferInstance inferInstance
    (objectSourceDerived f V)
    (objectTargetDerived f V)
    (objectSource f V)
    (objectTarget f V)
    (moduleLocalization.{z} X)
    (objectSourceUnit f V)
    (objectTargetUnit f V)
    (ModuleQis.{z} X)
    inferInstance
    (objectSource_isRightDerived f V)
    (objectPushforwardDerivedNat f V)

/-- The objectwise derived comparison is an isomorphism. -/
@[stacks 0D6H "derived objectwise sections comparison isomorphism"]
theorem objectPushforwardComparison_isIso
    (f : X.Hom Y) (V : Y)
    [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]
    [IsGrothendieckAbelian (ModuleCat.{z} X)]
    [IsGrothendieckAbelian (ModuleCat.{z} Y)] :
    IsIso (objectPushforwardComparison f V) := sorry

/-- The objectwise derived comparison as a natural isomorphism. -/
@[stacks 0D6H "derived objectwise sections comparison isomorphism"]
noncomputable def objectPushforwardComparisonIso (f : X.Hom Y) (V : Y)
    [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]
    [IsGrothendieckAbelian (ModuleCat.{z} X)]
    [IsGrothendieckAbelian (ModuleCat.{z} Y)] :
    objectSourceDerived f V ≅ objectTargetDerived f V :=
  @asIso _ inferInstance _ _ (objectPushforwardComparison f V)
    (objectPushforwardComparison_isIso f V)

/-- Each object component of the objectwise derived comparison is invertible. -/
@[stacks 0D6H "derived objectwise sections comparison component"]
theorem objectPushforwardComparison_app_isIso
    (f : X.Hom Y) (V : Y)
    [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]
    [IsGrothendieckAbelian (ModuleCat.{z} X)]
    [IsGrothendieckAbelian (ModuleCat.{z} Y)]
    (K : ModuleDerived.{z} X) :
    IsIso ((objectPushforwardComparison f V).app K) := sorry

end ModuleSections

end RingedSite.Hom
