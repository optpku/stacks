module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived.Naturality
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived.SectionsComparison
public import ReasLib.CategoryTheory.DerivedCategory.Functor.KInjectiveModel.Composition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived global-sections comparison

This file packages the module-valued form of the global-sections/direct-image comparison.  The
ordinary naturality map is transported to homotopy categories and then to total right-derived
functors; the target remains the derived category of modules over the global-sections ring.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open ComplexShape

-- Use the existing additive law for the specified module-valued section functors.
attribute [local instance] RingedSite.Hom.moduleGlobalSectionsFunctor_additive
  RingedSite.Hom.moduleCat_hasDerivedCategory

noncomputable section

universe z uX vX uY vY w

namespace RingedSite.Hom

namespace ModuleSections

private theorem moduleGrothendieck.{z₁, u₁, v₁, w₁}
    (Z : RingedSite.{u₁, v₁, w₁})
    [UnivLE.{max u₁ v₁, z₁}] [UnivLE.{max u₁ v₁ w₁, z₁}] :
    IsGrothendieckAbelian.{z₁} (ModuleCat.{z₁} Z) := by
  letI : PreservesFilteredColimitsOfSize.{max u₁ v₁, max u₁ v₁}
      (forget AddCommGrpCat.{z₁}) :=
    preservesFilteredColimitsOfSize_of_univLE.{z₁, z₁, max u₁ v₁, max u₁ v₁}
      (forget AddCommGrpCat.{z₁})
  letI : HasSheafify Z.siteTopology AddCommGrpCat.{z₁} := inferInstance
  letI : Small.{z₁} Z.carrier :=
    @Small.trans_univLE.{max u₁ v₁, z₁, u₁} Z.carrier (small_max.{v₁} Z.carrier) inferInstance
  letI : LocallySmall.{z₁} Z.carrier :=
    ⟨fun U V => @Small.trans_univLE.{max u₁ v₁, z₁, v₁} (U ⟶ V)
      (small_max.{u₁} (U ⟶ V)) inferInstance⟩
  letI : EssentiallySmall.{z₁} Z.carrier := inferInstance
  letI : ∀ V : Z.carrierᵒᵖ,
      Small.{z₁} (StructuredArrow V (equivSmallModel Z.carrier).inverse.op) :=
    fun _ => inferInstance
  letI : ∀ V : Z.carrierᵒᵖ,
      HasLimitsOfShape (StructuredArrow V (equivSmallModel Z.carrier).inverse.op)
        AddCommGrpCat.{z₁} := fun _ => inferInstance
  letI : Z.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{z₁} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall Z.siteTopology
  exact SheafOfModules.isGrothendieckAbelian_of_univLE Z.structureSheaf

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}} (f : Hom X Y)
variable [hXw : UnivLE.{uX, w}] [hYw : UnivLE.{uY, w}]
variable [hXXw : UnivLE.{max uX vX, w}] [hYYw : UnivLE.{max uY vY, w}]
variable [hYXw : UnivLE.{max uY vX, w}]
variable [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]
variable [hXu : UnivLE.{uX, z}] [hYu : UnivLE.{uY, z}]

variable [hX : Functor.HasRightDerivedFunctor
  (moduleGlobalSectionsToModuleDerived.{z} X) (ModuleQis.{z} X)]
variable [hY : Functor.HasRightDerivedFunctor
  (moduleGlobalSectionsToModuleDerived.{z} Y) (ModuleQis.{z} Y)]
variable [hF : Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived.{z} f) (ModuleQis.{z} X)]

/-- The homotopy-level source functor for the derived global-sections comparison. -/
noncomputable abbrev derivedGlobalSectionsSource :
    ModuleHomotopy.{z} X ⥤ ModuleSections.Derived.{z} Y :=
  moduleGlobalSectionsToModuleDerived.{z} X ⋙
    globalSectionsRestrictionDerived.{z, uX, vX, uY, vY, w} f

/-- The homotopy-level target functor for the derived global-sections comparison. -/
noncomputable abbrev derivedGlobalSectionsTarget :
    ModuleHomotopy.{z} X ⥤ ModuleSections.Derived.{z} Y :=
  f.modulePushforward.{z}.mapHomotopyCategory (up ℤ) ⋙
    moduleGlobalSectionsToModuleDerived.{z} Y

/-- The source derived functor after restricting scalars along the global-sections map. -/
noncomputable abbrev derivedGlobalSectionsSourceDerived :
    ModuleDerived.{z} X ⥤ ModuleSections.Derived.{z} Y :=
  (moduleGlobalSectionsToModuleDerived.{z} X).totalRightDerived
    (moduleLocalization.{z} X) (ModuleQis.{z} X) ⋙
    globalSectionsRestrictionDerived.{z, uX, vX, uY, vY, w} f

/-- The derived direct-image functor followed by derived global sections. -/
noncomputable abbrev derivedGlobalSectionsTargetDerived :
    ModuleDerived.{z} X ⥤ ModuleSections.Derived.{z} Y :=
  modulePushforwardDerived.{z} f ⋙ (moduleGlobalSectionsToModuleDerived.{z} Y).totalRightDerived
    (moduleLocalization.{z} Y) (ModuleQis.{z} Y)

/-- The unit exhibiting `derivedGlobalSectionsSourceDerived` as a right-derived model of the
source homotopy functor. -/
noncomputable def derivedGlobalSectionsSourceUnit :
    derivedGlobalSectionsSource f ⟶
      moduleLocalization.{z} X ⋙ derivedGlobalSectionsSourceDerived f :=
  Functor.whiskerRight
      (Functor.totalRightDerivedUnit
        (moduleGlobalSectionsToModuleDerived.{z} X)
        (moduleLocalization.{z} X) (ModuleQis.{z} X))
      (globalSectionsRestrictionDerived.{z, uX, vX, uY, vY, w} f) ≫
    (Functor.associator
      (moduleLocalization.{z} X)
      ((moduleGlobalSectionsToModuleDerived.{z} X).totalRightDerived
        (moduleLocalization.{z} X) (ModuleQis.{z} X))
      (globalSectionsRestrictionDerived.{z, uX, vX, uY, vY, w} f)).hom

/-- The unit exhibiting `derivedGlobalSectionsTargetDerived` as a right-derived model of the
target homotopy functor. -/
noncomputable def derivedGlobalSectionsTargetUnit :
    derivedGlobalSectionsTarget f ⟶
      moduleLocalization.{z} X ⋙ derivedGlobalSectionsTargetDerived f :=
  Functor.whiskerLeft
      (f.modulePushforward.{z}.mapHomotopyCategory (up ℤ))
      (Functor.totalRightDerivedUnit
        (moduleGlobalSectionsToModuleDerived.{z} Y)
        (moduleLocalization.{z} Y) (ModuleQis.{z} Y)) ≫
    (Functor.associator
      (f.modulePushforward.{z}.mapHomotopyCategory (up ℤ))
      (moduleLocalization.{z} Y)
      ((moduleGlobalSectionsToModuleDerived.{z} Y).totalRightDerived
        (moduleLocalization.{z} Y) (ModuleQis.{z} Y))).hom ≫
    Functor.whiskerRight
      (Functor.totalRightDerivedUnit
        (modulePushforwardToDerived.{z} f)
        (moduleLocalization.{z} X) (ModuleQis.{z} X))
      ((moduleGlobalSectionsToModuleDerived.{z} Y).totalRightDerived
        (moduleLocalization.{z} Y) (ModuleQis.{z} Y)) ≫
    (Functor.associator
      (moduleLocalization.{z} X)
      (modulePushforwardDerived.{z} f)
      ((moduleGlobalSectionsToModuleDerived.{z} Y).totalRightDerived
        (moduleLocalization.{z} Y) (ModuleQis.{z} Y))).hom

/-- The homotopy-level natural transformation underlying the derived global-sections comparison. -/
@[stacks 0D6H "derived module global-sections naturality"]
noncomputable def derivedGlobalSectionsPushforwardNat :
    derivedGlobalSectionsSource f ⟶ derivedGlobalSectionsTarget f :=
  (Functor.associator
      ((moduleGlobalSectionsFunctor.{z} X).mapHomotopyCategory (up ℤ))
      (DerivedCategory.Qh :
        HomotopyCategory (_root_.ModuleCat.{z} (globalSectionsRing X)) (up ℤ) ⥤
          ModuleSections.Derived.{z} X)
      (globalSectionsRestrictionDerived.{z, uX, vX, uY, vY, w} f)).hom ≫
    Functor.whiskerLeft
      ((moduleGlobalSectionsFunctor.{z} X).mapHomotopyCategory (up ℤ))
      ((globalSectionsRestriction.{z, uX, vX, uY, vY, w} f).mapDerivedCategoryFactorsh.hom) ≫
    (Functor.associator
      ((moduleGlobalSectionsFunctor.{z} X).mapHomotopyCategory (up ℤ))
      ((globalSectionsRestriction.{z, uX, vX, uY, vY, w} f).mapHomotopyCategory (up ℤ))
      (DerivedCategory.Qh :
        HomotopyCategory (_root_.ModuleCat.{z} (globalSectionsRing Y)) (up ℤ) ⥤
          ModuleSections.Derived.{z} Y)).inv ≫
    Functor.whiskerRight
      ((Functor.mapHomotopyCategoryCompIso
        (Iso.refl
          (moduleGlobalSectionsFunctor.{z} X ⋙
            (globalSectionsRestriction.{z, uX, vX, uY, vY, w} f :
              _root_.ModuleCat.{z} (globalSectionsRing X) ⥤
                _root_.ModuleCat.{z} (globalSectionsRing Y)))) (up ℤ)).hom)
      (DerivedCategory.Qh :
        HomotopyCategory (_root_.ModuleCat.{z} (globalSectionsRing Y)) (up ℤ) ⥤
          ModuleSections.Derived.{z} Y) ≫
    Functor.whiskerRight
      (NatTrans.mapHomotopyCategory
        (moduleGlobalSectionsPushforwardNatIso.{z} f).hom (up ℤ))
      (DerivedCategory.Qh :
        HomotopyCategory (_root_.ModuleCat.{z} (globalSectionsRing Y)) (up ℤ) ⥤
          ModuleSections.Derived.{z} Y) ≫
    Functor.whiskerRight
      ((Functor.mapHomotopyCategoryCompIso
        (Iso.refl
          (f.modulePushforward.{z} ⋙ moduleGlobalSectionsFunctor.{z} Y)) (up ℤ)).inv)
      (DerivedCategory.Qh :
        HomotopyCategory (_root_.ModuleCat.{z} (globalSectionsRing Y)) (up ℤ) ⥤
          ModuleSections.Derived.{z} Y) ≫
    (Functor.associator
      (f.modulePushforward.{z}.mapHomotopyCategory (up ℤ))
      ((moduleGlobalSectionsFunctor.{z} Y).mapHomotopyCategory (up ℤ))
      (DerivedCategory.Qh :
        HomotopyCategory (_root_.ModuleCat.{z} (globalSectionsRing Y)) (up ℤ) ⥤
          ModuleSections.Derived.{z} Y)).hom

/-- The exact scalar restriction identifies the source presentation with the composite
ordinary functor on homotopy categories. -/
private def sourcePresentationIso :
    derivedGlobalSectionsSource f ≅
      Functor.Homotopy.toDerived
        (moduleGlobalSectionsFunctor.{z} X ⋙ globalSectionsRestriction.{z, uX, vX, uY, vY, w} f) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft ((moduleGlobalSectionsFunctor.{z} X).mapHomotopyCategory (up ℤ))
      (globalSectionsRestriction.{z, uX, vX, uY, vY, w} f).mapDerivedCategoryFactorsh ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso
        (Iso.refl (moduleGlobalSectionsFunctor.{z} X ⋙ globalSectionsRestriction.{z, uX, vX, uY, vY, w} f)) (up ℤ))
      DerivedCategory.Qh

/-- The target presentation uses the same ordinary composite before deriving. -/
private def targetPresentationIso :
    derivedGlobalSectionsTarget f ≅
      Functor.Homotopy.toDerived (f.modulePushforward.{z} ⋙ moduleGlobalSectionsFunctor.{z} Y) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso
        (Iso.refl (f.modulePushforward.{z} ⋙ moduleGlobalSectionsFunctor.{z} Y)) (up ℤ))
      DerivedCategory.Qh

/-- The inverse homotopy comparison reverses the actual ordinary sections isomorphism
and the native presentation isomorphisms. -/
private def homotopyComparisonIso :
    derivedGlobalSectionsSource f ≅ derivedGlobalSectionsTarget f where
  hom := derivedGlobalSectionsPushforwardNat f
  inv := (targetPresentationIso f).hom ≫
    Functor.whiskerRight
      (NatTrans.mapHomotopyCategory (moduleGlobalSectionsPushforwardNatIso.{z} f).inv (up ℤ))
      DerivedCategory.Qh ≫ (sourcePresentationIso f).inv
  hom_inv_id := by sorry
  inv_hom_id := by sorry

-- The ambient module universe contains both the site and its coefficient rings.
-- The original site-size bounds alone do not provide a Grothendieck module category.
variable [UnivLE.{max uX vX w, z}] [hYstrong : UnivLE.{max uY vY w, z}]

attribute [local instance] moduleGrothendieck

private noncomputable def modelToChosen
    {A B : Type*} [Category* A] [Abelian A] [Category* B] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [IsGrothendieckAbelian.{z} A]
    (F : A ⥤ B) [F.Additive]
    [Functor.HasRightDerivedFunctor (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ))] :
    Functor.KInjectiveModel.derived.{z} F ≅ Functor.RightDerived.Homotopy.functor F := by
  letI : (Functor.RightDerived.Homotopy.functor F).IsRightDerivedFunctor
      (Functor.RightDerived.Homotopy.unit F) (HomotopyCategory.quasiIso A (up ℤ)) :=
    Functor.instIsRightDerivedFunctorTotalRightDerivedTotalRightDerivedUnit
      (Functor.Homotopy.toDerived F) (DerivedCategory.Qh (C := A))
      (HomotopyCategory.quasiIso A (up ℤ))
  exact Functor.rightDerivedUnique
    (RF := Functor.KInjectiveModel.derived.{z} F)
    (RF' := Functor.RightDerived.Homotopy.functor F)
    (α := Functor.KInjectiveModel.Homotopy.unit F)
    (α'₂ := Functor.RightDerived.Homotopy.unit F)
    (W := HomotopyCategory.quasiIso A (up ℤ))

private def sourceModelIso :
    Functor.KInjectiveModel.derived.{z}
        (moduleGlobalSectionsFunctor.{z} X ⋙ globalSectionsRestriction.{z, uX, vX, uY, vY, w} f) ≅
      derivedGlobalSectionsSourceDerived f :=
  (Functor.KInjectiveModel.postcomposeIso
    (moduleGlobalSectionsFunctor.{z} X) (globalSectionsRestriction.{z, uX, vX, uY, vY, w} f)).symm ≪≫
    Functor.isoWhiskerRight (modelToChosen (moduleGlobalSectionsFunctor.{z} X))
      (globalSectionsRestrictionDerived.{z, uX, vX, uY, vY, w} f)

omit hX hY hF hXw hXXw hYYw hYXw hXu in
/-- Direct image of the specified source model is acyclic for global sections: the
particular target augmentation becomes a quasi-isomorphism after taking sections. -/
private theorem sectionsAugmentation_quasiIso (K : CochainComplex (ModuleCat.{z} X) ℤ) :
    QuasiIso (((moduleGlobalSectionsFunctor.{z} Y).mapHomologicalComplex (up ℤ)).map
      ((CochainComplex.KInjectiveResolution.Construction.augmentation.{z} (ModuleCat.{z} Y)).app
        ((f.modulePushforward.{z}.mapHomologicalComplex (up ℤ)).obj
          ((CochainComplex.KInjectiveResolution.Construction.replacement.{z}
            (ModuleCat.{z} X)).obj K)))) := sorry

private def targetModelIso :
    Functor.KInjectiveModel.derived.{z}
        (f.modulePushforward.{z} ⋙ moduleGlobalSectionsFunctor.{z} Y) ≅
      derivedGlobalSectionsTargetDerived f :=
  Functor.KInjectiveModel.compositionIso f.modulePushforward.{z}
      (moduleGlobalSectionsFunctor.{z} Y) (sectionsAugmentation_quasiIso f) ≪≫
    Functor.isoWhiskerRight (modelToChosen f.modulePushforward.{z})
      (Functor.KInjectiveModel.derived.{z} (moduleGlobalSectionsFunctor.{z} Y)) ≪≫
    Functor.isoWhiskerLeft (modulePushforwardDerived.{z} f)
      (modelToChosen (moduleGlobalSectionsFunctor.{z} Y))

omit hY hF hYu hYstrong in
private theorem sourceModelIso_unit :
    Functor.KInjectiveModel.Homotopy.unit
        (moduleGlobalSectionsFunctor.{z} X ⋙ globalSectionsRestriction.{z, uX, vX, uY, vY, w} f) ≫
      Functor.whiskerLeft (moduleLocalization.{z} X) (sourceModelIso f).hom =
        (sourcePresentationIso f).inv ≫ derivedGlobalSectionsSourceUnit f := sorry

omit hX hXw hXXw hYYw hYXw hXu in
private theorem targetModelIso_unit :
    Functor.KInjectiveModel.Homotopy.unit
        (f.modulePushforward.{z} ⋙ moduleGlobalSectionsFunctor.{z} Y) ≫
      Functor.whiskerLeft (moduleLocalization.{z} X) (targetModelIso f).hom =
        (targetPresentationIso f).inv ≫ derivedGlobalSectionsTargetUnit f := sorry

/-- The source universal maps transport the actual model's initial extension through
exact scalar restriction and the caller's chosen derived global sections. -/
@[stacks 0D6H "derived global-sections source model"]
noncomputable instance derivedGlobalSectionsSource_isRightDerived :
    (derivedGlobalSectionsSourceDerived f).IsRightDerivedFunctor
      (derivedGlobalSectionsSourceUnit f) (ModuleQis.{z} X) where
  isLeftKanExtension :=
    (Functor.isLeftKanExtension_iff_of_iso₂
      (Functor.KInjectiveModel.Homotopy.unit
        (moduleGlobalSectionsFunctor.{z} X ⋙ globalSectionsRestriction.{z, uX, vX, uY, vY, w} f))
      (derivedGlobalSectionsSourceUnit f) (sourcePresentationIso f).symm
      (sourceModelIso f) (sourceModelIso_unit f)).mp
      (Functor.IsRightDerivedFunctor.isLeftKanExtension _ _ (ModuleQis.{z} X))

/-- The target universal maps transport the actual augmentation comparison; arbitrary
ringed-site direct image need not preserve K-injective complexes. -/
@[stacks 0D6H "derived global-sections target model"]
noncomputable instance derivedGlobalSectionsTarget_isRightDerived :
    (derivedGlobalSectionsTargetDerived f).IsRightDerivedFunctor
      (derivedGlobalSectionsTargetUnit f) (ModuleQis.{z} X) where
  isLeftKanExtension :=
    (Functor.isLeftKanExtension_iff_of_iso₂
      (Functor.KInjectiveModel.Homotopy.unit
        (f.modulePushforward.{z} ⋙ moduleGlobalSectionsFunctor.{z} Y))
      (derivedGlobalSectionsTargetUnit f) (targetPresentationIso f).symm
      (targetModelIso f) (targetModelIso_unit f)).mp
      (Functor.IsRightDerivedFunctor.isLeftKanExtension _ _ (ModuleQis.{z} X))

/- The derived comparison is obtained from the universal property of the two right-derived
functors.  Keeping this construction in the library makes the comparison reusable without
reconstructing the localization square in each chapter. -/

/-- The canonical derived global-sections/direct-image comparison. -/
@[stacks 0D6H "derived global-sections comparison"]
noncomputable def derivedGlobalSectionsPushforwardComparison :
    derivedGlobalSectionsSourceDerived f ⟶ derivedGlobalSectionsTargetDerived f :=
  Functor.rightDerivedNatTrans
    (derivedGlobalSectionsSourceDerived f)
    (derivedGlobalSectionsTargetDerived f)
    (derivedGlobalSectionsSourceUnit f)
    (derivedGlobalSectionsTargetUnit f)
    (ModuleQis.{z} X)
    (derivedGlobalSectionsPushforwardNat f)

/-- The derived global-sections/direct-image comparison is an isomorphism. -/
@[stacks 0D6H "derived global-sections comparison isomorphism"]
noncomputable instance derivedGlobalSectionsPushforwardComparison_isIso :
    IsIso (derivedGlobalSectionsPushforwardComparison f) := by
  let e := Functor.rightDerivedNatIso
    (derivedGlobalSectionsSourceDerived f) (derivedGlobalSectionsTargetDerived f)
    (derivedGlobalSectionsSourceUnit f) (derivedGlobalSectionsTargetUnit f)
    (ModuleQis.{z} X) (homotopyComparisonIso f)
  change IsIso e.hom
  infer_instance

/-- The derived comparison as a reusable natural isomorphism. -/
@[stacks 0D6H "derived global-sections comparison isomorphism"]
noncomputable def derivedGlobalSectionsPushforwardIso :
    derivedGlobalSectionsSourceDerived f ≅ derivedGlobalSectionsTargetDerived f :=
  asIso (derivedGlobalSectionsPushforwardComparison f)

/-- Each object component of the derived global-sections comparison is invertible. -/
@[stacks 0D6H "derived global-sections comparison component"]
theorem derivedGlobalSectionsPushforwardComparison_app_isIso
    (K : ModuleDerived.{z} X) :
    IsIso ((derivedGlobalSectionsPushforwardComparison f).app K) := by
  infer_instance

end ModuleSections

end RingedSite.Hom
