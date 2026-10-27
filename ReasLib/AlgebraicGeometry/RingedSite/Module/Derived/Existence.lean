/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.CoefficientLift
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CellReplacement.Functorial
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.TensorScalarExtension
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback.KFlat
public import Mathlib.CategoryTheory.Localization.Opposite
public import ReasLib.CategoryTheory.Functor.Derived.Deformation
public import ReasLib.CategoryTheory.DerivedCategory.Functor.KInjectiveModel.Homotopy

/-! # Derived module functors with lifted coefficients -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

set_option backward.privateInPublic true
set_option backward.isDefEq.respectTransparency false

universe u

namespace RingedSite.Hom.DerivedExistence

/-- Lifting coefficients without changing module sections is additive. -/
private instance coefficientForwardAdditive (X : RingedSite.{u + 1, u + 1, u}) :
    (SheafOfModules.CoefficientLift.equivalence X.structureSheaf).functor.Additive where
  map_add := by intros; ext V m; rfl

/-- Lowering coefficients without changing module sections is additive. -/
private instance coefficientInverseAdditive (X : RingedSite.{u + 1, u + 1, u}) :
    (SheafOfModules.CoefficientLift.equivalence X.structureSheaf).inverse.Additive where
  map_add := by intros; ext V m; rfl

/-- The original site equipped with its lifted coefficient rings. -/
private def liftedSite (X : RingedSite.{u + 1, u + 1, u}) :
    RingedSite.{u + 1, u + 1, u + 1} :=
  RingedSite.ofRingSheaf X.siteTopology
    (SheafOfModules.CoefficientLift.ring X.structureSheaf)

/-- The same underlying site map with its ring maps lifted coefficientwise. -/
private def liftedHom {X Y : RingedSite.{u + 1, u + 1, u}} (f : Hom X Y) :
    Hom (liftedSite X) (liftedSite Y) where
  base := f.base
  isMorphismOfSites := f.isMorphismOfSites
  structureSheafMap := ⟨Functor.whiskerRight f.structureSheafMap.hom
    SheafOfModules.UniverseLift.ringFunctor⟩

/-- Coefficient lifting commutes with the actual module direct image through identity functions. -/
private def pushforwardCoefficientIso {X Y : RingedSite.{u + 1, u + 1, u}}
    (f : Hom X Y) :
    (SheafOfModules.CoefficientLift.equivalence X.structureSheaf).functor ⋙
        (liftedHom f).modulePushforward.{u + 1} ≅
      f.modulePushforward.{u + 1} ⋙
        (SheafOfModules.CoefficientLift.equivalence Y.structureSheaf).functor :=
  NatIso.ofComponents (fun M ↦
    let P := ((SheafOfModules.CoefficientLift.equivalence X.structureSheaf).functor ⋙
      (liftedHom f).modulePushforward.{u + 1}).obj M
    let Q := (f.modulePushforward.{u + 1} ⋙
      (SheafOfModules.CoefficientLift.equivalence Y.structureSheaf).functor).obj M
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun V ↦
        { hom := ModuleCat.ofHom (X := P.val.obj V) (Y := Q.val.obj V)
            { toFun := fun m ↦ m
              map_add' := fun _ _ ↦ rfl
              map_smul' := fun _ _ ↦ rfl }
          inv := ModuleCat.ofHom (X := Q.val.obj V) (Y := P.val.obj V)
            { toFun := fun m ↦ m
              map_add' := fun _ _ ↦ rfl
              map_smul' := fun _ _ ↦ rfl }
          hom_inv_id := by ext m; rfl
          inv_hom_id := by ext m; rfl }) (fun {_ _} g ↦ by ext m; rfl)))
    (fun g ↦ by ext V m; rfl)

/-- Equal-universe module direct image has its concrete presheaf-and-sheafification adjoint. -/
private theorem liftedRightAdjoint {X Y : RingedSite.{u + 1, u + 1, u}}
    (f : Hom X Y) [HasWeakSheafify X.siteTopology AddCommGrpCat.{u + 1}]
    [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] :
    ((liftedHom f).modulePushforward.{u + 1}).IsRightAdjoint := by
  dsimp [modulePushforward]
  infer_instance

/-- Lowering coefficients commutes with module direct image by identity section maps. -/
private def pushforwardInverseIso {X Y : RingedSite.{u + 1, u + 1, u}}
    (f : Hom X Y) :
    (SheafOfModules.CoefficientLift.equivalence X.structureSheaf).inverse ⋙
        f.modulePushforward.{u + 1} ≅
      (liftedHom f).modulePushforward.{u + 1} ⋙
        (SheafOfModules.CoefficientLift.equivalence Y.structureSheaf).inverse :=
  NatIso.ofComponents (fun M ↦
    let P := ((SheafOfModules.CoefficientLift.equivalence X.structureSheaf).inverse ⋙
      f.modulePushforward.{u + 1}).obj M
    let Q := ((liftedHom f).modulePushforward.{u + 1} ⋙
      (SheafOfModules.CoefficientLift.equivalence Y.structureSheaf).inverse).obj M
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun V ↦
        { hom := ModuleCat.ofHom (X := P.val.obj V) (Y := Q.val.obj V)
            { toFun := fun m ↦ m
              map_add' := fun _ _ ↦ rfl
              map_smul' := fun _ _ ↦ rfl }
          inv := ModuleCat.ofHom (X := Q.val.obj V) (Y := P.val.obj V)
            { toFun := fun m ↦ m
              map_add' := fun _ _ ↦ rfl
              map_smul' := fun _ _ ↦ rfl }
          hom_inv_id := by ext m; rfl
          inv_hom_id := by ext m; rfl }) (fun {_ _} g ↦ by ext m; rfl)))
    (fun g ↦ by ext V m; rfl)

/-- The actual adjunction comparisons identify coefficient transport of module inverse image. -/
private def pullbackCoefficientIso {X Y : RingedSite.{u + 1, u + 1, u}}
    (f : Hom X Y) [(f.modulePushforward.{u + 1}).IsRightAdjoint]
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{u + 1}]
    [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] :
    f.modulePullback.{u + 1} ⋙
        (SheafOfModules.CoefficientLift.equivalence X.structureSheaf).functor ≅
      (SheafOfModules.CoefficientLift.equivalence Y.structureSheaf).functor ⋙
        (@modulePullback.{u + 1} _ _ (liftedHom f) (liftedRightAdjoint f)) :=
  Adjunction.leftAdjointUniq
    (((modulePullbackPushforwardAdjunction.{u + 1} f).comp
      (SheafOfModules.CoefficientLift.equivalence X.structureSheaf).toAdjunction).ofNatIsoRight
        (pushforwardInverseIso f))
    ((SheafOfModules.CoefficientLift.equivalence Y.structureSheaf).toAdjunction.comp
      (@modulePullbackPushforwardAdjunction.{u + 1} _ _ (liftedHom f)
        (liftedRightAdjoint f)))

/-- Coefficient transport applied degreewise is an equivalence of the original cochain categories. -/
private def coefficientComplex (X : RingedSite.{u + 1, u + 1, u}) :=
  (SheafOfModules.CoefficientLift.equivalence X.structureSheaf).mapHomologicalComplex
    (ComplexShape.up ℤ)

/-- The displayed equal-universe cell model transported back to the original coefficients. -/
private def replacement (X : RingedSite.{u + 1, u + 1, u})
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{u + 1}]
    [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] :
    CochainComplex (ModuleCat.{u + 1} X) ℤ ⥤ CochainComplex (ModuleCat.{u + 1} X) ℤ :=
  (coefficientComplex X).functor ⋙ SheafOfModules.CellReplacement.functor ⋙
    (coefficientComplex X).inverse

/-- The transported augmentation is the actual cell augmentation followed by coefficient lowering. -/
private def augmentation (X : RingedSite.{u + 1, u + 1, u})
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{u + 1}]
    [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] :
    replacement X ⟶ 𝟭 (CochainComplex (ModuleCat.{u + 1} X) ℤ) :=
  Functor.whiskerLeft (coefficientComplex X).functor
    (Functor.whiskerRight SheafOfModules.CellReplacement.augmentationNatTrans
      (coefficientComplex X).inverse) ≫
    (coefficientComplex X).unitIso.inv

/-- The transported cell augmentation remains a quasi-isomorphism. -/
private theorem augmentation_quasiIso (X : RingedSite.{u + 1, u + 1, u})
    [HasSheafify X.siteTopology AddCommGrpCat.{u + 1}]
    [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    (K : CochainComplex (ModuleCat.{u + 1} X) ℤ) :
    QuasiIso ((augmentation X).app K) := by
  -- Local instance justification (proof-local temporary data): use the displayed cell augmentation law for this particular complex when mapping it through the equivalence.
  letI hc := SheafOfModules.CellReplacement.augmentation_quasiIso
    ((coefficientComplex X).functor.obj K)
  -- Local instance justification (proof-local temporary data): compose this mapped augmentation with the equivalence unit at the same complex.
  letI hm : QuasiIso ((coefficientComplex X).inverse.map
      (SheafOfModules.CellReplacement.augmentation
        ((coefficientComplex X).functor.obj K))) := by
    change QuasiIso (((SheafOfModules.CoefficientLift.equivalence X.structureSheaf).inverse.mapHomologicalComplex
      (ComplexShape.up ℤ)).map _)
    exact HomologicalComplex.quasiIso_map_of_preservesHomology _
      (SheafOfModules.CoefficientLift.equivalence X.structureSheaf).inverse
  change QuasiIso (((coefficientComplex X).inverse.map
    (SheafOfModules.CellReplacement.augmentation ((coefficientComplex X).functor.obj K))) ≫
      (coefficientComplex X).unitIso.inv.app K)
  exact quasiIso_comp _ _

/-- The lifted section rings retain the original multiplicative commutativity. -/
private def liftedCommSheaf (X : RingedSite.{u + 1, u + 1, u})
    (hX : ∀ V (x y : X.structureSheaf.obj.obj V), x * y = y * x) :
    Sheaf X.siteTopology CommRingCat.{u + 1} :=
  ⟨SheafOfModules.TensorScalarExtension.commView
    (SheafOfModules.CoefficientLift.ring X.structureSheaf).obj
    (fun V x y ↦ congrArg ULift.up (hX V x.down y.down)), by
      apply Presheaf.isSheaf_of_isSheaf_comp _ _ (forget₂ CommRingCat RingCat)
      exact (SheafOfModules.CoefficientLift.ring X.structureSheaf).property⟩

/-- The coefficient-lifted complex viewed over the commutative coefficient sheaf. -/
private abbrev commComplex (X : RingedSite.{u + 1, u + 1, u})
    (hX : ∀ V (x y : X.structureSheaf.obj.obj V), x * y = y * x)
    (K : CochainComplex (ModuleCat.{u + 1} X) ℤ) :
    CochainComplex (SheafOfModules.RingedSite.ringedSiteModuleCategory
      X.siteTopology (liftedCommSheaf X hX)) ℤ :=
  (coefficientComplex X).functor.obj K

/-- Good complexes are K-flat with flat terms after the unchanged-carrier coefficient transport. -/
private def good (X : RingedSite.{u + 1, u + 1, u})
    (hX : ∀ V (x y : X.structureSheaf.obj.obj V), x * y = y * x)
    (K : CochainComplex (ModuleCat.{u + 1} X) ℤ) : Prop :=
  (commComplex X hX K).IsKFlat ∧
    HomologicalComplex.IsTermwiseFlat (commComplex X hX K)

/-- Every transported replacement is good by the actual coefficient-equivalence counit. -/
private theorem replacement_good (X : RingedSite.{u + 1, u + 1, u})
    (hX : ∀ V (x y : X.structureSheaf.obj.obj V), x * y = y * x)
    [HasSheafify X.siteTopology AddCommGrpCat.{u + 1}]
    [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    (K : CochainComplex (ModuleCat.{u + 1} X) ℤ) :
    good X hX ((replacement X).obj K) := by
  let e := (coefficientComplex X).counitIso.app
    (SheafOfModules.CellReplacement.model ((coefficientComplex X).functor.obj K))
  refine ⟨HomologicalComplex.IsKFlat.of_iso ?_ e.symm,
    HomologicalComplex.IsTermwiseFlat.of_iso ?_ e.symm⟩
  · exact SheafOfModules.RingedSite.CellReplacement.model_isKFlat
      (O := liftedCommSheaf X hX) (commComplex X hX K)
  · exact SheafOfModules.RingedSite.CellReplacement.model_termwiseFlat
      (O := liftedCommSheaf X hX) (commComplex X hX K)

/-- Pullback inverts quasi-isomorphisms between the displayed coefficient-transported good complexes. -/
private theorem map_good_quasiIso {X Y : RingedSite.{u + 1, u + 1, u}}
    (f : Hom X Y) [(f.modulePushforward.{u + 1}).IsRightAdjoint]
    (hX : ∀ V (x y : X.structureSheaf.obj.obj V), x * y = y * x)
    (hY : ∀ V (x y : Y.structureSheaf.obj.obj V), x * y = y * x)
    [HasSheafify X.siteTopology AddCommGrpCat.{u + 1}]
    [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    [HasSheafify Y.siteTopology AddCommGrpCat.{u + 1}]
    [Y.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    {K L : CochainComplex (ModuleCat.{u + 1} Y) ℤ}
    (hK : good Y hY K) (hL : good Y hY L) (α : K ⟶ L) (hα : QuasiIso α) :
    QuasiIso ((modulePullbackComplex.{u + 1} f).map α) := by
  let fl : Hom (ofCommRingSheaf X.siteTopology (liftedCommSheaf X hX))
      (ofCommRingSheaf Y.siteTopology (liftedCommSheaf Y hY)) := liftedHom f
  have hα' : QuasiIso ((coefficientComplex Y).functor.map α) :=
    by
      -- Local instance justification (proof-local temporary data): the supplied input quasi-isomorphism is transported through this coefficient equivalence alone.
      letI := hα
      exact HomologicalComplex.quasiIso_map_of_preservesHomology α
        (SheafOfModules.CoefficientLift.equivalence Y.structureSheaf).functor
  -- Local instance justification (proof-local temporary data): the explicitly lifted map needs its completed adjoint certificate for the K-flat pullback comparison.
  letI : (fl.modulePushforward.{u + 1}).IsRightAdjoint := liftedRightAdjoint f
  have high : QuasiIso ((modulePullbackComplex.{u + 1} fl).map
      ((coefficientComplex Y).functor.map α)) :=
    modulePullbackComplex.map_quasiIso fl hK.1 hK.2 hL.1 hL.2 _ hα'
  let e := NatIso.mapHomologicalComplex (pullbackCoefficientIso f) (ComplexShape.up ℤ)
  have low : QuasiIso ((coefficientComplex X).functor.map
      ((modulePullbackComplex.{u + 1} f).map α)) :=
    (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoMk (e.app K) (e.app L) (e.hom.naturality α).symm)).mpr high
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _
    (SheafOfModules.CoefficientLift.equivalence X.structureSheaf).functor).mp low

/-- Naturality of the actual augmentation carries quasi-isomorphisms to replacement maps. -/
private theorem replacement_map_quasiIso (Y : RingedSite.{u + 1, u + 1, u})
    [HasSheafify Y.siteTopology AddCommGrpCat.{u + 1}]
    [Y.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    {K L : CochainComplex (ModuleCat.{u + 1} Y) ℤ} (α : K ⟶ L) (hα : QuasiIso α) :
    QuasiIso ((replacement Y).map α) := by
  -- Local instance justification (proof-local temporary data): the three specified quasi-isomorphisms are used only in this augmentation naturality square.
  letI := hα
  -- Local instance justification (proof-local temporary data): cancel the displayed source augmentation in this single naturality square.
  letI := augmentation_quasiIso Y K
  -- Local instance justification (proof-local temporary data): cancel the displayed target augmentation in this single naturality square.
  letI := augmentation_quasiIso Y L
  apply (quasiIso_iff_comp_right ((replacement Y).map α) ((augmentation Y).app L)).mp
  rw [(augmentation Y).naturality α]
  change QuasiIso ((augmentation Y).app K ≫ α)
  exact quasiIso_comp _ _

section PullbackModel

variable {X Y : RingedSite.{u + 1, u + 1, u}} (f : Hom X Y)
  [(f.modulePushforward.{u + 1}).IsRightAdjoint]
  (hX : ∀ V (x y : X.structureSheaf.obj.obj V), x * y = y * x)
  (hY : ∀ V (x y : Y.structureSheaf.obj.obj V), x * y = y * x)
  [HasSheafify X.siteTopology AddCommGrpCat.{u + 1}]
  [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  [HasSheafify Y.siteTopology AddCommGrpCat.{u + 1}]
  [Y.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]

include hX hY

/-- Pullback on the displayed replacements inverts the original quasi-isomorphisms. -/
private theorem replacementPullback_inverts :
    (HomologicalComplex.quasiIso (ModuleCat.{u + 1} Y) (ComplexShape.up ℤ)).IsInvertedBy
      (replacement Y ⋙ HomotopyCategory.quotient _ (ComplexShape.up ℤ) ⋙
        modulePullbackToDerived.{u + 1} f) := by
  intro K L α hα
  apply (NatIso.isIso_map_iff
    (Functor.isoWhiskerLeft (replacement Y)
      (Functor.Homotopy.cochainIso (f.modulePullback.{u + 1}))) α).mpr
  have hp := map_good_quasiIso f hX hY
    (replacement_good Y hY K) (replacement_good Y hY L)
    ((replacement Y).map α) (replacement_map_quasiIso Y α hα)
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr hp

/-- The same augmentation is acyclic when its input is already a replacement. -/
private theorem pullback_augmentation_isIso (K : CochainComplex (ModuleCat.{u + 1} Y) ℤ) :
    IsIso ((HomotopyCategory.quotient _ (ComplexShape.up ℤ) ⋙
      modulePullbackToDerived.{u + 1} f).map ((augmentation Y).app ((replacement Y).obj K))) := by
  apply (NatIso.isIso_map_iff (Functor.Homotopy.cochainIso (f.modulePullback.{u + 1})) _).mpr
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr
    (map_good_quasiIso f hX hY
      (replacement_good Y hY ((replacement Y).obj K)) (replacement_good Y hY K)
      _ (augmentation_quasiIso Y ((replacement Y).obj K)))

/-- Localization of the actual replaced pullback cochain functor. -/
private def pullbackFunctor : ModuleDerived.{u + 1} Y ⥤ ModuleDerived.{u + 1} X :=
  Localization.lift (replacement Y ⋙ HomotopyCategory.quotient _ (ComplexShape.up ℤ) ⋙
    modulePullbackToDerived.{u + 1} f) (replacementPullback_inverts f hX hY)
      (DerivedCategory.Q (C := ModuleCat.{u + 1} Y))

/-- The localization comparison computes derived pullback on the displayed replacements. -/
private def pullbackComputation :
    (HomotopyCategory.quotient _ (ComplexShape.up ℤ) ⋙ moduleLocalization.{u + 1} Y) ⋙
        pullbackFunctor f hX hY ≅
      replacement Y ⋙ (HomotopyCategory.quotient _ (ComplexShape.up ℤ) ⋙
        modulePullbackToDerived.{u + 1} f) :=
  Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso _) (pullbackFunctor f hX hY) ≪≫
    Localization.fac _ (replacementPullback_inverts f hX hY) _

/-- The localization model retains the transported cell functor, its augmentation and its
specified universal extension maps. -/
private def pullbackModel :
    Functor.LeftDerived.Model (modulePullbackToDerived.{u + 1} f)
      (moduleLocalization.{u + 1} Y) (ModuleQis.{u + 1} Y) := by
  let q := HomotopyCategory.quotient (ModuleCat.{u + 1} Y) (ComplexShape.up ℤ)
  let L := moduleLocalization.{u + 1} Y
  let U := HomologicalComplex.quasiIso (ModuleCat.{u + 1} Y) (ComplexShape.up ℤ)
  -- Local instance justification (defeq pin): the composite quotient uses the same standard localization as the displayed compatibility derived category.
  letI : (q ⋙ L).IsLocalization U :=
    Functor.IsLocalization.of_iso _ (DerivedCategory.quotientCompQhIso _).symm
  exact Functor.LeftDerived.Deformation.modelOnLocalizedSource q
    (HomologicalComplex.homotopyEquivalences _ _) L _ U
    (replacement Y) (augmentation Y) (augmentation_quasiIso Y)
    (modulePullbackToDerived.{u + 1} f) (pullbackFunctor f hX hY) (pullbackComputation f hX hY)
    (pullback_augmentation_isIso f hX hY)

/-- Precomposition of the descended counit recovers the specified augmentation comparison. -/
private theorem pullbackCounit_cochains :
    (Functor.associator (HomotopyCategory.quotient _ (ComplexShape.up ℤ))
      (moduleLocalization.{u + 1} Y) (pullbackFunctor f hX hY)).hom ≫
        Functor.whiskerLeft (HomotopyCategory.quotient _ (ComplexShape.up ℤ))
          (pullbackModel f hX hY).counit =
      Functor.LeftDerived.Deformation.counit
        (HomotopyCategory.quotient _ (ComplexShape.up ℤ) ⋙ moduleLocalization.{u + 1} Y)
        (replacement Y) (augmentation Y)
        (HomotopyCategory.quotient _ (ComplexShape.up ℤ) ⋙ modulePullbackToDerived.{u + 1} f)
        (pullbackFunctor f hX hY) (pullbackComputation f hX hY) := by
  ext K
  simp [pullbackModel, Functor.LeftDerived.Deformation.modelOnLocalizedSource,
    Localization.liftNatTrans_app]

/-- Unbounded derived inverse image exists, with universal maps supplied by the displayed
cell replacement and its unchanged-carrier coefficient transport. -/
theorem hasPullback :
    (modulePullbackToDerived.{u + 1} f).HasLeftDerivedFunctor (ModuleQis.{u + 1} Y) := by
  let M := pullbackModel f hX hY
  -- Local instance justification (proof-local temporary data): this existence certificate records the already constructed model's actual terminal-extension witness.
  letI := M.isLeftDerived
  exact Functor.HasLeftDerivedFunctor.mk' (LF := M.functor) (α := M.counit)

universe h vH

/-- Postcomposition retains the actual augmentation-based terminal-extension maps. -/
private theorem pullbackModel_postcompose {H : Type h} [Category.{vH} H]
    (G : ModuleDerived.{u + 1} X ⥤ H) :
    ((pullbackModel f hX hY).functor ⋙ G).IsLeftDerivedFunctor
      ((Functor.associator (moduleLocalization.{u + 1} Y)
        (pullbackModel f hX hY).functor G).inv ≫
          Functor.whiskerRight (pullbackModel f hX hY).counit G) (ModuleQis.{u + 1} Y) := by
  let q := HomotopyCategory.quotient (ModuleCat.{u + 1} Y) (ComplexShape.up ℤ)
  let L := moduleLocalization.{u + 1} Y
  let U := HomologicalComplex.quasiIso (ModuleCat.{u + 1} Y) (ComplexShape.up ℤ)
  let F := modulePullbackToDerived.{u + 1} f
  let T := (pullbackModel f hX hY).functor
  let ε := (Functor.associator L T G).inv ≫
    Functor.whiskerRight (pullbackModel f hX hY).counit G
  let e : (q ⋙ L) ⋙ (T ⋙ G) ≅ replacement Y ⋙ ((q ⋙ F) ⋙ G) :=
    (Functor.associator (q ⋙ L) T G).symm ≪≫
      Functor.isoWhiskerRight (pullbackComputation f hX hY) G ≪≫
      Functor.associator (replacement Y) (q ⋙ F) G
  -- Local instance justification (defeq pin): this is the composite standard localization already used by the original augmented replacement model.
  letI : (q ⋙ L).IsLocalization U :=
    Functor.IsLocalization.of_iso _ (DerivedCategory.quotientCompQhIso _).symm
  have hε : (Functor.associator q L (T ⋙ G)).hom ≫ Functor.whiskerLeft q ε =
      Functor.LeftDerived.Deformation.counit (q ⋙ L) (replacement Y) (augmentation Y)
        ((q ⋙ F) ⋙ G) (T ⋙ G) e := by
    ext K
    have h₀ := NatTrans.congr_app (pullbackCounit_cochains f hX hY) K
    change 𝟙 _ ≫ (𝟙 _ ≫ G.map ((pullbackModel f hX hY).counit.app (q.obj K))) =
      (𝟙 _ ≫ G.map ((pullbackComputation f hX hY).hom.app K) ≫ 𝟙 _) ≫
        G.map ((q ⋙ F).map ((augmentation Y).app K)) ≫ 𝟙 _
    have h₁ : (pullbackModel f hX hY).counit.app (q.obj K) =
        (pullbackComputation f hX hY).hom.app K ≫
          (q ⋙ F).map ((augmentation Y).app K) := by
      change 𝟙 _ ≫ (pullbackModel f hX hY).counit.app (q.obj K) =
        (pullbackComputation f hX hY).hom.app K ≫
          (q ⋙ F).map ((augmentation Y).app K) ≫ 𝟙 _ at h₀
      exact (Category.id_comp _).symm.trans (h₀.trans
        (congrArg (fun a ↦ (pullbackComputation f hX hY).hom.app K ≫ a)
          (Category.comp_id _)))
    calc
      _ = G.map ((pullbackModel f hX hY).counit.app (q.obj K)) :=
        (Category.id_comp _).trans (Category.id_comp _)
      _ = G.map ((pullbackComputation f hX hY).hom.app K) ≫
          G.map ((q ⋙ F).map ((augmentation Y).app K)) :=
        (congrArg (fun a ↦ G.map a) h₁).trans (G.map_comp _ _)
      _ = _ := by simp only [Category.id_comp, Category.comp_id]
  have hAug (K : CochainComplex (ModuleCat.{u + 1} Y) ℤ) :
      IsIso (((q ⋙ F) ⋙ G).map ((augmentation Y).app ((replacement Y).obj K))) := by
    -- Local instance justification (proof-local temporary data): the already specified acyclic augmentation is mapped through this particular postcomposition functor.
    letI := pullback_augmentation_isIso f hX hY K
    exact Functor.map_isIso G _
  let w := Functor.LeftDerived.Deformation.terminalWitness (q ⋙ L) U
    (replacement Y) (augmentation Y) (augmentation_quasiIso Y)
    ((q ⋙ F) ⋙ G) (T ⋙ G) e hAug
  exact ⟨⟨⟨Functor.LeftDerived.Deformation.terminalWitnessOfPrecomp q
    (HomologicalComplex.homotopyEquivalences _ _) L (F ⋙ G) (T ⋙ G) ε
      (hε.symm ▸ w)⟩⟩⟩

/-- The canonical total left-derived functor inherits the displayed absolute comparison. -/
private theorem pullback_postcompose {H : Type h} [Category.{vH} H]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived.{u + 1} f) (ModuleQis.{u + 1} Y)]
    (G : ModuleDerived.{u + 1} X ⥤ H) :
    (modulePullbackDerived.{u + 1} f ⋙ G).IsLeftDerivedFunctor
      ((Functor.associator (moduleLocalization.{u + 1} Y)
        (modulePullbackDerived.{u + 1} f) G).inv ≫
          Functor.whiskerRight ((modulePullbackToDerived.{u + 1} f).totalLeftDerivedCounit
            (moduleLocalization.{u + 1} Y) (ModuleQis.{u + 1} Y)) G)
      (ModuleQis.{u + 1} Y) := by
  let M := pullbackModel f hX hY
  -- Local instance justification (proof-local temporary data): compare the actual replacement model with the canonical total-derived model.
  letI := M.isLeftDerived
  let e := Functor.leftDerivedUnique (LF := M.functor)
    (LF' := modulePullbackDerived.{u + 1} f) (α := M.counit)
    (α'₂ := (modulePullbackToDerived.{u + 1} f).totalLeftDerivedCounit
      (moduleLocalization.{u + 1} Y) (ModuleQis.{u + 1} Y)) (W := ModuleQis.{u + 1} Y)
  apply (Functor.isLeftDerivedFunctor_iff_of_iso (LF := M.functor ⋙ G)
    (LF' := modulePullbackDerived.{u + 1} f ⋙ G)
    (W := ModuleQis.{u + 1} Y) (e := Functor.isoWhiskerRight e G)
    (α := (Functor.associator _ _ G).inv ≫ Functor.whiskerRight M.counit G)
    (α' := (Functor.associator _ _ G).inv ≫ Functor.whiskerRight
      ((modulePullbackToDerived.{u + 1} f).totalLeftDerivedCounit
        (moduleLocalization.{u + 1} Y) (ModuleQis.{u + 1} Y)) G)
    ?_).mp (pullbackModel_postcompose f hX hY G)
  ext K
  have h := NatTrans.congr_app (Functor.leftDerivedNatTrans_fac M.functor
    (modulePullbackDerived.{u + 1} f) M.counit
    ((modulePullbackToDerived.{u + 1} f).totalLeftDerivedCounit
      (moduleLocalization.{u + 1} Y) (ModuleQis.{u + 1} Y))
    (ModuleQis.{u + 1} Y) (𝟙 _)) K
  change G.map (e.hom.app ((moduleLocalization.{u + 1} Y).obj K)) ≫
    (𝟙 _ ≫ G.map _) = 𝟙 _ ≫ G.map _
  rw [Category.id_comp, Category.id_comp, ← G.map_comp]
  exact congrArg (fun a ↦ G.map a) (h.trans (Category.comp_id _))

end PullbackModel

section DualWitness

universe c₁ c₂ c₃ v₁ v₂ v₃

/-- Opposite universal extension maps give the dual universal maps with their original components. -/
private def dualWitness {C : Type c₁} {D : Type c₂} {H : Type c₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} H]
    (L : C ⥤ D) (F : C ⥤ H) (T : D ⥤ H) (c : (L ⋙ T).op ⟶ F.op)
    (w : (Functor.RightExtension.mk (L := L.op) (F := F.op) T.op c).IsUniversal) :
    (Functor.LeftExtension.mk T c.removeOp).IsUniversal := by
  let lift (E : Functor.LeftExtension L F) : T ⟶ E.right :=
    (w.lift (Functor.RightExtension.mk E.right.op (NatTrans.op E.hom))).removeOp
  have fac (E : Functor.LeftExtension L F) :
      c.removeOp ≫ Functor.whiskerLeft L (lift E) = E.hom := by
    ext A
    exact congrArg (fun t ↦ (t.app (Opposite.op A)).unop)
      (w.fac (Functor.RightExtension.mk E.right.op (NatTrans.op E.hom)))
  refine IsInitial.ofUniqueHom (fun E ↦ StructuredArrow.homMk (lift E) (fac E)) ?_
  intro E m
  apply StructuredArrow.hom_ext
  have hm : Functor.whiskerLeft L.op (NatTrans.op m.right) ≫ c = (NatTrans.op E.hom) := by
    ext A
    exact congrArg (fun t ↦ (t.app A.unop).op) (StructuredArrow.w m)
  have h := w.hom_ext (hm.trans (w.fac
    (Functor.RightExtension.mk E.right.op (NatTrans.op E.hom))).symm)
  ext A
  exact congrArg (fun t ↦ (t.app (Opposite.op A)).unop) h

end DualWitness

section RightModel

universe w uC vC uD vD wC wD h vH

variable {C : Type uC} [Category.{vC} C] [Abelian C]
  [IsGrothendieckAbelian.{w} C] [HasDerivedCategory.{wC} C]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
  (F : C ⥤ D) [F.Additive]

/-- The K-injective deformation supplies actual initial extension maps after postcomposition. -/
private theorem rightModel_postcompose {H : Type h} [Category.{vH} H]
    (G : DerivedCategory D ⥤ H) :
    (Functor.KInjectiveModel.derived F ⋙ G).IsRightDerivedFunctor
      (Functor.whiskerRight (Functor.KInjectiveModel.Homotopy.unit F) G ≫
        (Functor.associator DerivedCategory.Qh (Functor.KInjectiveModel.derived F) G).hom)
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) := by
  let q := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  let L := DerivedCategory.Qh (C := C)
  let U := HomologicalComplex.quasiIso C (ComplexShape.up ℤ)
  let R := CochainComplex.KInjectiveResolution.Construction.replacement.{w} C
  let η := CochainComplex.KInjectiveResolution.Construction.augmentation.{w} C
  let T := Functor.KInjectiveModel.derived F
  let FH := Functor.Homotopy.toDerived F
  let α := Functor.whiskerRight (Functor.KInjectiveModel.Homotopy.unit F) G ≫
    (Functor.associator L T G).hom
  let e₀ : (q ⋙ L) ⋙ T ≅ R ⋙ (q ⋙ FH) :=
    Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso C) T ≪≫
      Functor.KInjectiveModel.fac F ≪≫
      Functor.isoWhiskerLeft R (Functor.Homotopy.cochainIso F).symm
  let e : (q ⋙ L) ⋙ (T ⋙ G) ≅ R ⋙ ((q ⋙ FH) ⋙ G) :=
    (Functor.associator (q ⋙ L) T G).symm ≪≫
      Functor.isoWhiskerRight e₀ G ≪≫ Functor.associator R (q ⋙ FH) G
  -- Local instance justification (defeq pin): opposite deformation uses precisely the original standard composite localization on cochain complexes.
  letI : (q ⋙ L).IsLocalization U :=
    Functor.IsLocalization.of_iso _ (DerivedCategory.quotientCompQhIso C).symm
  have hη (A : (CochainComplex C ℤ)ᵒᵖ) : U.op ((NatTrans.op η).app A) :=
    CochainComplex.KInjectiveResolution.Construction.augmentation_quasiIso C A.unop
  have hAug (A : (CochainComplex C ℤ)ᵒᵖ) :
      IsIso ((((q ⋙ FH) ⋙ G).op).map ((NatTrans.op η).app (R.op.obj A))) := by
    -- Local instance justification (proof-local temporary data): both endpoints of this augmentation are the specified K-injective replacements.
    letI : (R.obj A.unop).IsKInjective :=
      CochainComplex.KInjectiveResolution.Construction.replacement_isKInjective C A.unop
    -- Local instance justification (proof-local temporary data): the second endpoint is the replacement of the first specified K-injective model.
    letI : (R.obj (R.obj A.unop)).IsKInjective :=
      CochainComplex.KInjectiveResolution.Construction.replacement_isKInjective C
        (R.obj A.unop)
    let φ : R.obj A.unop ⟶ R.obj (R.obj A.unop) := η.app (R.obj A.unop)
    have ht := (CochainComplex.IsKInjective.quasiIso_iff φ).mp
        (CochainComplex.KInjectiveResolution.Construction.augmentation_quasiIso C
          (R.obj A.unop))
    have hi := HomotopyCategory.quotient_inverts_homotopyEquivalences
      C (ComplexShape.up ℤ) _ ht
    -- Local instance justification (proof-local temporary data): map this actual homotopy equivalence through the displayed functors and then take its opposite.
    letI := hi
    change IsIso ((G.map (FH.map (q.map (η.app (R.obj A.unop))))).op)
    infer_instance
  have hα : (Functor.associator q.op L.op (T ⋙ G).op).hom ≫
      Functor.whiskerLeft q.op (NatTrans.op α) =
      Functor.LeftDerived.Deformation.counit (q ⋙ L).op R.op (NatTrans.op η)
        ((q ⋙ FH) ⋙ G).op (T ⋙ G).op (NatIso.op e.symm) := by
    ext A
    apply Quiver.Hom.unop_inj
    change (G.map ((Functor.KInjectiveModel.Homotopy.unit F).app (q.obj A.unop)) ≫
        𝟙 _) ≫ 𝟙 _ =
      (𝟙 _ ≫ G.map ((q ⋙ FH).map (η.app A.unop))) ≫ e.inv.app A.unop
    simp only [e, Iso.trans_inv, Iso.symm_inv, Functor.isoWhiskerRight_inv,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_inv_app,
      Functor.associator_hom_app, Category.id_comp, Category.comp_id]
    rw [← G.map_comp]
    apply congrArg (fun a ↦ G.map a)
    change (Functor.KInjectiveModel.Homotopy.unitOnCochains F).app A.unop = _
    change (Functor.Homotopy.cochainIso F).hom.app A.unop ≫
        (𝟙 _ ≫ (Functor.KInjectiveModel.ordinaryCochain F).map (η.app A.unop) ≫
          (Functor.KInjectiveModel.fac F).inv.app A.unop) ≫
        T.map ((DerivedCategory.quotientCompQhIso C).inv.app A.unop) ≫ 𝟙 _ =
      (q ⋙ FH).map (η.app A.unop) ≫
        ((Functor.Homotopy.cochainIso F).hom.app (R.obj A.unop) ≫
          (Functor.KInjectiveModel.fac F).inv.app A.unop) ≫
        T.map ((DerivedCategory.quotientCompQhIso C).inv.app A.unop)
    simp only [Category.id_comp, Category.comp_id, Category.assoc]
    exact ((Functor.Homotopy.cochainIso F).hom.naturality_assoc
      (η.app A.unop) ((Functor.KInjectiveModel.fac F).inv.app A.unop ≫
        T.map ((DerivedCategory.quotientCompQhIso C).inv.app A.unop))).symm
  let w := Functor.LeftDerived.Deformation.terminalWitness (q ⋙ L).op U.op
    R.op (NatTrans.op η) hη ((q ⋙ FH) ⋙ G).op (T ⋙ G).op (NatIso.op e.symm) hAug
  let w' := Functor.LeftDerived.Deformation.terminalWitnessOfPrecomp q.op
    (HomologicalComplex.homotopyEquivalences C (ComplexShape.up ℤ)).op
    L.op (FH ⋙ G).op (T ⋙ G).op (NatTrans.op α) (hα.symm ▸ w)
  exact ⟨⟨⟨dualWitness L (FH ⋙ G) (T ⋙ G) (NatTrans.op α) w'⟩⟩⟩

/-- Any specified right-derived model inherits the actual postcomposed K-injective witness. -/
private theorem right_postcompose {H : Type h} [Category.{vH} H]
    (RF : DerivedCategory C ⥤ DerivedCategory D)
    (β : Functor.Homotopy.toDerived F ⟶ DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor β (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]
    (G : DerivedCategory D ⥤ H) :
    (RF ⋙ G).IsRightDerivedFunctor (Functor.whiskerRight β G ≫
      (Functor.associator DerivedCategory.Qh RF G).hom)
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) := by
  let T := Functor.KInjectiveModel.derived F
  let α := Functor.KInjectiveModel.Homotopy.unit F
  let W := HomotopyCategory.quasiIso C (ComplexShape.up ℤ)
  let e := Functor.rightDerivedUnique (RF := T) (RF' := RF) (α := α) (α'₂ := β) (W := W)
  apply (Functor.isRightDerivedFunctor_iff_of_iso (RF := T ⋙ G) (RF' := RF ⋙ G)
    (α := Functor.whiskerRight α G ≫ (Functor.associator _ T G).hom)
    (α' := Functor.whiskerRight β G ≫ (Functor.associator _ RF G).hom)
    (W := W) (e := Functor.isoWhiskerRight e G) ?_).mp (rightModel_postcompose F G)
  ext K
  have h := NatTrans.congr_app (Functor.rightDerivedNatTrans_fac T RF α β W (𝟙 _)) K
  change (G.map (α.app K) ≫ 𝟙 _) ≫ G.map (e.hom.app (DerivedCategory.Qh.obj K)) =
    G.map (β.app K) ≫ 𝟙 _
  rw [Category.comp_id, Category.comp_id, ← G.map_comp]
  exact congrArg (fun a ↦ G.map a) (h.trans (Category.id_comp _))

end RightModel

/-- The canonical total derived module functors form an absolute-derived pair, using the
displayed coefficient-transported cell model and the actual K-injective replacement. -/
theorem hasPair {X Y : RingedSite.{u + 1, u + 1, u}} (f : Hom X Y)
    [(f.modulePushforward.{u + 1}).IsRightAdjoint]
    (hX : ∀ V (x y : X.structureSheaf.obj.obj V), x * y = y * x)
    (hY : ∀ V (x y : Y.structureSheaf.obj.obj V), x * y = y * x)
    [HasSheafify X.siteTopology AddCommGrpCat.{u + 1}]
    [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    [HasSheafify Y.siteTopology AddCommGrpCat.{u + 1}]
    [Y.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    [IsGrothendieckAbelian.{u + 1} (ModuleCat.{u + 1} X)]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived.{u + 1} f) (ModuleQis.{u + 1} Y)]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived.{u + 1} f) (ModuleQis.{u + 1} X)] :
    DerivedAdjunction.HasPair.{u + 1} f where
  toIsLeftDerivedFunctor := pullback_postcompose f hX hY (modulePushforwardDerived.{u + 1} f)
  toIsRightDerivedFunctor := right_postcompose (f.modulePushforward.{u + 1})
    (modulePushforwardDerived.{u + 1} f)
    ((modulePushforwardToDerived.{u + 1} f).totalRightDerivedUnit
      (moduleLocalization.{u + 1} X) (ModuleQis.{u + 1} X)) (modulePullbackDerived.{u + 1} f)

end RingedSite.Hom.DerivedExistence
