/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.Comparison
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CellReplacement.Functorial
public import ReasLib.CategoryTheory.Functor.Derived.Deformation
public import Mathlib.CategoryTheory.Sites.LeftExact
public import ReasLib.CategoryTheory.Sites.TypeSheafification

/-! # Cell models for derived pullback over sheaves of rings -/

set_option backward.privateInPublic true

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape

noncomputable section

universe u v w t

namespace RingedSite.ToposHom.DerivedPullbackCellModel

private instance (priority := 50) addLimits [UnivLE.{t, w}] :
    HasLimitsOfSize.{t, t} AddCommGrpCat.{w} :=
  hasLimitsOfSizeOfUnivLE.{w, w, t, t} _

private instance (priority := 50) typeLimits [UnivLE.{t, w}] :
    HasLimitsOfSize.{t, t} (Type w) :=
  hasLimitsOfSizeOfUnivLE.{w, w, t, t} _

private instance (priority := 50) addColimits [UnivLE.{t, w}] :
    HasColimitsOfSize.{t, t} AddCommGrpCat.{w} :=
  hasColimitsOfSizeOfUnivLE.{w, w, t, t} _

private instance (priority := 50) typeColimits [UnivLE.{t, w}] :
    HasColimitsOfSize.{t, t} (Type w) :=
  hasColimitsOfSizeOfUnivLE.{w, w, t, t} _

private instance (priority := 50) forgetLimits [UnivLE.{t, w}] :
    PreservesLimitsOfSize.{t, t} (forget AddCommGrpCat.{w}) :=
  @preservesLimitsOfSize_of_univLE _ _ _ _ (forget AddCommGrpCat.{w})
    (inferInstance : UnivLE.{t, w}) (inferInstance : UnivLE.{t, w})
    (inferInstance : PreservesLimitsOfSize.{w, w} (forget AddCommGrpCat.{w}))

private instance (priority := 50) forgetFiltered [UnivLE.{t, w}] :
    PreservesFilteredColimitsOfSize.{t, t} (forget AddCommGrpCat.{w}) :=
  @preservesFilteredColimitsOfSize_of_univLE _ _ _ _ (forget AddCommGrpCat.{w})
    (inferInstance : UnivLE.{t, w}) (inferInstance : UnivLE.{t, w})
    (inferInstance : PreservesFilteredColimitsOfSize.{w, w} (forget AddCommGrpCat.{w}))

private instance forgetCoverColimits {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) [UnivLE.{max u v, w}] (U : C) :
    PreservesColimitsOfShape (J.Cover U)ᵒᵖ (forget AddCommGrpCat.{w}) :=
  @PreservesFilteredColimitsOfSize.preserves_filtered_colimits _ _ _ _
    (forget AddCommGrpCat.{w}) (inferInstance : PreservesFilteredColimitsOfSize.{max u v, max u v}
      (forget AddCommGrpCat.{w})) _ _
    (@isFiltered_op_of_isCofiltered _ _
      (isCofiltered_of_semilatticeInf_nonempty (J.Cover U)))

private instance typeW {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) [UnivLE.{max u v, w}]
    [HasWeakSheafify J (Type w)] : J.WEqualsLocallyBijective (Type w) :=
  GrothendieckTopology.type_WEqualsLocallyBijective_of_univLE J

private instance addW {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) [UnivLE.{max u v, w}]
    [HasWeakSheafify J AddCommGrpCat.{w}] [HasWeakSheafify J (Type w)]
    [J.PreservesSheafification (forget AddCommGrpCat.{w})] :
    J.WEqualsLocallyBijective AddCommGrpCat.{w} := by
  refine @GrothendieckTopology.WEqualsLocallyBijective.mk' C _ J
    AddCommGrpCat.{w} _ _ _ _ _ _ _ _ ?_ ?_
  · intro P
    apply (Presheaf.isLocallyInjective_forget_iff J (toSheafify J P)).mp
    exact (J.W_of_preservesSheafification (forget AddCommGrpCat.{w}) _
      (J.W_toSheafify P)).isLocallyInjective
  · intro P
    apply (Presheaf.isLocallySurjective_iff_whisker_forget J (toSheafify J P)).mpr
    exact (J.W_of_preservesSheafification (forget AddCommGrpCat.{w}) _
      (J.W_toSheafify P)).isLocallySurjective

variable {X Y Z : RingedSite.{u, v, w}}
variable [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [Y.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [Z.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [UnivLE.{max u v, w}]

private theorem sheafify (X : RingedSite.{u, v, w}) :
    HasSheafify X.siteTopology AddCommGrpCat.{w} := by infer_instance

private theorem locallyBijective (X : RingedSite.{u, v, w}) :
    X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w} :=
  @addW X.carrier _ X.siteTopology inferInstance
    (sheafify X).isRightAdjoint inferInstance
    (GrothendieckTopology.instPreservesSheafification X.siteTopology (forget AddCommGrpCat.{w}))

private def replacement (X : RingedSite.{u, v, w}) :
    CochainComplex (ModuleCat.{w} X) ℤ ⥤ CochainComplex (ModuleCat.{w} X) ℤ :=
  @SheafOfModules.CellReplacement.functor _ _ _ X.structureSheaf
    (sheafify X).isRightAdjoint (locallyBijective X)

private def augmentation (X : RingedSite.{u, v, w}) :
    replacement X ⟶ 𝟭 (CochainComplex (ModuleCat.{w} X) ℤ) :=
  @SheafOfModules.CellReplacement.augmentationNatTrans _ _ _ X.structureSheaf
    (sheafify X).isRightAdjoint (locallyBijective X)

private theorem augmentationQuasiIso (X : RingedSite.{u, v, w})
    (K : CochainComplex (ModuleCat.{w} X) ℤ) : QuasiIso ((augmentation X).app K) :=
  @SheafOfModules.CellReplacement.augmentation_quasiIso _ _ _ X.structureSheaf
    (sheafify X).isRightAdjoint (locallyBijective X) K (sheafify X)

/-- Localization of module complexes in the standard derived category. -/
abbrev Q (X : RingedSite.{u, v, w}) :
    CochainComplex (ModuleCat.{w} X) ℤ ⥤ Hom.ModuleDerived.{w} X :=
  @DerivedCategory.Q _ _ _ (Hom.moduleCat_hasDerivedCategory.{w} X)

variable (f : ToposHom X Y)
variable [(SheafOfModules.restrictScalars.{w} f.structureMap).IsRightAdjoint]

/-- Pull back the functorial cell replacement degree by degree. -/
def cochain : CochainComplex (ModuleCat.{w} Y) ℤ ⥤
    CochainComplex (ModuleCat.{w} X) ℤ := (replacement Y) ⋙ f.modulePullbackComplex

/-- Localized pullback of cell replacements inverts quasi-isomorphisms. -/
theorem invertsQuasiIso :
    (HomologicalComplex.quasiIso (ModuleCat.{w} Y) (up ℤ)).IsInvertedBy
      (cochain f ⋙ Q X) := sorry

/-- The localization of the pulled-back cell replacement. -/
def functor : Hom.ModuleDerived.{w} Y ⥤ Hom.ModuleDerived.{w} X :=
  Localization.lift (cochain f ⋙ Q X) (invertsQuasiIso f) (Q Y)

/-- Evaluation of the localized cell model on an input complex. -/
def computation : Q Y ⋙ functor f ≅ cochain f ⋙ Q X :=
  Localization.fac (cochain f ⋙ Q X) (invertsQuasiIso f) (Q Y)

/-- Pullback of the augmentation on a cell replacement is a quasi-isomorphism. -/
theorem augmentationOnModels_quasiIso (K : CochainComplex (ModuleCat.{w} Y) ℤ) :
    QuasiIso (f.modulePullbackComplex.map
      ((augmentation Y).app ((replacement Y).obj K))) := sorry

/-- The quotient functor from module complexes to their homotopy category. -/
abbrev quotient (X : RingedSite.{u, v, w}) :=
  HomotopyCategory.quotient (ModuleCat.{w} X) (up ℤ)

private def sourceComparison :
    quotient Y ⋙ modulePullbackToDerived f ≅ f.modulePullbackComplex ⋙ Q X :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (@Functor.mapHomotopyCategoryFactors _ _ _ _ _ _ _ f.modulePullback
        (modulePullback_additive f) (up ℤ)) (Hom.moduleLocalization X) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft f.modulePullbackComplex
      (@DerivedCategory.quotientCompQhIso _ _ _ (Hom.moduleCat_hasDerivedCategory.{w} X))

private def modelComputation :
    (quotient Y ⋙ Hom.moduleLocalization Y) ⋙ functor f ≅
      (replacement Y) ⋙ (quotient Y ⋙ modulePullbackToDerived f) :=
  Functor.isoWhiskerRight
      (@DerivedCategory.quotientCompQhIso _ _ _ (Hom.moduleCat_hasDerivedCategory.{w} Y))
      (functor f) ≪≫
    computation f ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (replacement Y) (sourceComparison f).symm

private theorem quotientLocalization (X : RingedSite.{u, v, w}) :
    (quotient X ⋙ Hom.moduleLocalization X).IsLocalization
      (HomologicalComplex.quasiIso (ModuleCat.{w} X) (up ℤ)) :=
  Functor.IsLocalization.of_iso
    (HomologicalComplex.quasiIso (ModuleCat.{w} X) (up ℤ))
    (@DerivedCategory.quotientCompQhIso _ _ _ (Hom.moduleCat_hasDerivedCategory.{w} X)).symm

/-- The cell model with the augmentation-based universal extension maps. -/
def pullbackModel : Functor.LeftDerived.Model (modulePullbackToDerived f)
    (Hom.moduleLocalization Y) (Hom.ModuleQis Y) :=
  @Functor.LeftDerived.Deformation.modelOnLocalizedSource _ _ _ _ _ _ _ _
    (quotient Y) (HomologicalComplex.homotopyEquivalences _ _) inferInstance
    (Hom.moduleLocalization Y) (Hom.ModuleQis Y) inferInstance
    (HomologicalComplex.quasiIso (ModuleCat.{w} Y) (up ℤ))
    (quotientLocalization Y)
    (replacement Y) (augmentation Y)
    (fun K ↦ augmentationQuasiIso Y K)
    (modulePullbackToDerived f) (functor f) (modelComputation f)
    (fun K ↦ (NatIso.isIso_map_iff (sourceComparison f) _).mpr
      (Localization.inverts (Q X)
        (HomologicalComplex.quasiIso (ModuleCat.{w} X) (up ℤ)) _
        (augmentationOnModels_quasiIso f K)))

/-- The cell-derived pullback agrees with the canonical total left derived pullback. -/
def canonicalIso [HasModulePullbackDerived f] :
    (pullbackModel f).functor ≅ f.modulePullbackDerived :=
  (pullbackModel f).iso
    ⟨f.modulePullbackDerived,
      (modulePullbackToDerived f).totalLeftDerivedCounit
        (Hom.moduleLocalization Y) (Hom.ModuleQis Y), inferInstance⟩

variable (g : ToposHom Y Z)
variable [(SheafOfModules.restrictScalars.{w} g.structureMap).IsRightAdjoint]
variable [HasModulePullbackDerived f] [HasModulePullbackDerived g]

/-- Pullback preserves the augmentation on a pulled-back cell model. -/
theorem augmentationOnPulledModels_quasiIso
    (K : CochainComplex (ModuleCat.{w} Z) ℤ) :
    QuasiIso (f.modulePullbackComplex.map
      ((augmentation Y).app
        (g.modulePullbackComplex.obj ((replacement Z).obj K)))) := sorry

private def canonicalComputation :
    Q Y ⋙ f.modulePullbackDerived ≅ cochain f ⋙ Q X :=
  Functor.isoWhiskerLeft (Q Y) (canonicalIso f).symm ≪≫ computation f

private def iteratedSourceComparison :
    quotient Z ⋙ (g.modulePullbackHomotopy ⋙ modulePullbackToDerived f) ≅
      (g.modulePullbackComplex ⋙ f.modulePullbackComplex) ⋙ Q X :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (@Functor.mapHomotopyCategoryFactors _ _ _ _ _ _ _ g.modulePullback
        (modulePullback_additive g) (up ℤ)) (modulePullbackToDerived f) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft g.modulePullbackComplex (sourceComparison f) ≪≫
    (Functor.associator _ _ _).symm

private def pulledAugmentationIso :
    cochain g ⋙ ((replacement Y) ⋙
      (f.modulePullbackComplex ⋙ Q X)) ≅
    cochain g ⋙ (f.modulePullbackComplex ⋙ Q X) :=
  NatIso.ofComponents
    (fun K ↦ Localization.isoOfHom (Q X)
      (HomologicalComplex.quasiIso (ModuleCat.{w} X) (up ℤ))
      (f.modulePullbackComplex.map
        ((augmentation Y).app ((cochain g).obj K)))
      (augmentationOnPulledModels_quasiIso f g K))
    (by
      intro K L a
      change (Q X).map (f.modulePullbackComplex.map
          ((replacement Y).map ((cochain g).map a))) ≫
          (Q X).map (f.modulePullbackComplex.map
            ((augmentation Y).app ((cochain g).obj L))) =
        (Q X).map (f.modulePullbackComplex.map
            ((augmentation Y).app ((cochain g).obj K))) ≫
          (Q X).map (f.modulePullbackComplex.map ((cochain g).map a))
      rw [← (Q X).map_comp, ← (Q X).map_comp,
        ← f.modulePullbackComplex.map_comp, ← f.modulePullbackComplex.map_comp]
      exact congrArg (fun t ↦ (Q X).map (f.modulePullbackComplex.map t))
        ((augmentation Y).naturality ((cochain g).map a)))

private def compositeComputation :
    Q Z ⋙ (g.modulePullbackDerived ⋙ f.modulePullbackDerived) ≅
      (replacement Z) ⋙
        (quotient Z ⋙ (g.modulePullbackHomotopy ⋙ modulePullbackToDerived f)) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (canonicalComputation g) f.modulePullbackDerived ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (cochain g) (canonicalComputation f) ≪≫
    Functor.isoWhiskerLeft (cochain g) (Functor.associator _ _ _) ≪≫
    pulledAugmentationIso f g ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft ((replacement Z))
      (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerLeft ((replacement Z))
      (iteratedSourceComparison f g).symm

private def compositeModelComputation :
    (quotient Z ⋙ Hom.moduleLocalization Z) ⋙
        (g.modulePullbackDerived ⋙ f.modulePullbackDerived) ≅
      (replacement Z) ⋙
        (quotient Z ⋙ (g.modulePullbackHomotopy ⋙ modulePullbackToDerived f)) :=
  Functor.isoWhiskerRight
      (@DerivedCategory.quotientCompQhIso _ _ _ (Hom.moduleCat_hasDerivedCategory.{w} Z))
      (g.modulePullbackDerived ⋙ f.modulePullbackDerived) ≪≫
    compositeComputation f g

/-- The transported cell-model counit is the composite of the two derived-pullback counits. -/
theorem compositeCounit_eq :
    Functor.LeftDerived.Deformation.counit
      (quotient Z ⋙ Hom.moduleLocalization Z)
      ((replacement Z))
      (augmentation Z)
      (quotient Z ⋙ (g.modulePullbackHomotopy ⋙ modulePullbackToDerived f))
      (g.modulePullbackDerived ⋙ f.modulePullbackDerived)
      (compositeModelComputation f g) =
    (Functor.associator (quotient Z) (Hom.moduleLocalization Z)
      (g.modulePullbackDerived ⋙ f.modulePullbackDerived)).hom ≫
      Functor.whiskerLeft (quotient Z)
        (CategoryTheory.SimplicialSites.derivedPullbackCompCounit f g) := sorry

/-- The fixed composite counit has universal extension maps constructed from cell augmentations. -/
def compositeTerminalWitness (h : ToposHom X Z)
    [(SheafOfModules.restrictScalars.{w} h.structureMap).IsRightAdjoint]
    (hcomp : h.modulePullback ≅ g.modulePullback ⋙ f.modulePullback) :
    (Functor.RightExtension.mk (g.modulePullbackDerived ⋙ f.modulePullbackDerived)
      (CategoryTheory.SimplicialSites.derivedPullbackCompCounit f g)).IsUniversal := by
  let e := Functor.isoWhiskerLeft (quotient Z)
      (CategoryTheory.SimplicialSites.derivedPullbackCompToDerivedIso f g h hcomp).symm ≪≫
    sourceComparison h
  let w := @Functor.LeftDerived.Deformation.terminalWitness _ _ _ _ _ _
    (quotient Z ⋙ Hom.moduleLocalization Z)
    (HomologicalComplex.quasiIso (ModuleCat.{w} Z) (up ℤ))
    (quotientLocalization Z)
    ((replacement Z))
    (augmentation Z)
    (fun K ↦ augmentationQuasiIso Z K)
    (quotient Z ⋙ (g.modulePullbackHomotopy ⋙ modulePullbackToDerived f))
    (g.modulePullbackDerived ⋙ f.modulePullbackDerived)
    (compositeModelComputation f g)
    (fun K ↦ (NatIso.isIso_map_iff e _).mpr
      (Localization.inverts (Q X)
        (HomologicalComplex.quasiIso (ModuleCat.{w} X) (up ℤ)) _
        (augmentationOnModels_quasiIso h K)))
  exact Functor.LeftDerived.Deformation.terminalWitnessOfPrecomp
    (quotient Z) (HomologicalComplex.homotopyEquivalences _ _)
    (Hom.moduleLocalization Z)
    (g.modulePullbackHomotopy ⋙ modulePullbackToDerived f)
    (g.modulePullbackDerived ⋙ f.modulePullbackDerived)
    (CategoryTheory.SimplicialSites.derivedPullbackCompCounit f g)
    (compositeCounit_eq f g ▸ w)

end RingedSite.ToposHom.DerivedPullbackCellModel
