/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SmallSheafification
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StructureSheaf.CommRing
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Localization.Equivalence

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

set_option backward.privateInPublic true
set_option maxHeartbeats 800000

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.Atlas

variable {S : Scheme.{u}} (X : AlgebraicSpace S)

/-- The small category of affine charts in the specified étale atlas. -/
abbrev Site := PullbackFactory.SmallAtlas.Site (AtlasInput.scheme X) (AtlasInput.map X)

/-- The topology induced on the affine charts of the atlas. -/
abbrev topology := PullbackFactory.SmallAtlas.topology (AtlasInput.scheme X) (AtlasInput.map X)

/-- The inclusion of the affine atlas charts in the étale site. -/
def inclusion : Site X ⥤ smallEtaleSite X :=
  PullbackFactory.SmallAtlas.inclusion (AtlasInput.scheme X) (AtlasInput.map X)

/-- The chosen affine atlas is a dense subsite of the étale site. -/
instance inclusion_dense : (inclusion X).IsDenseSubsite (topology X) (smallEtaleTopology X) :=
  PullbackFactory.SmallAtlas.denseSubsite _ _ (AtlasInput.locallySurjective X)

/-- Affine atlas charts cover every object of the étale site. -/
instance inclusion_coverDense : (inclusion X).IsCoverDense (smallEtaleTopology X) :=
  Functor.IsDenseSubsite.isCoverDense (topology X) (smallEtaleTopology X) (inclusion X)

/-- Étale morphisms between atlas charts locally lift through the atlas inclusion. -/
instance inclusion_locallyFull : (inclusion X).IsLocallyFull (smallEtaleTopology X) :=
  Functor.IsDenseSubsite.isLocallyFull (topology X) (smallEtaleTopology X) (inclusion X)

/-- The atlas inclusion detects equality of morphisms locally. -/
instance inclusion_locallyFaithful : (inclusion X).IsLocallyFaithful (smallEtaleTopology X) :=
  Functor.IsDenseSubsite.isLocallyFaithful (topology X) (smallEtaleTopology X) (inclusion X)

/-- The affine atlas inclusion is continuous for its induced topology. -/
instance inclusion_continuous : (inclusion X).IsContinuous (topology X) (smallEtaleTopology X) :=
  Functor.IsCoverDense.isContinuous (topology X) (smallEtaleTopology X) (inclusion X)
    (Functor.IsDenseSubsite.coverPreserving (topology X) (smallEtaleTopology X) (inclusion X))

/-- The restriction of the structure sheaf to the affine atlas charts. -/
def structureSheaf : Sheaf (topology X) RingCat.{u} :=
  ((inclusion X).sheafPushforwardContinuous RingCat.{u} (topology X)
    (smallEtaleTopology X)).obj (AlgebraicSpace.structureSheaf X)

private def additiveComparison :
    Sheaf (smallEtaleTopology X) AddCommGrpCat.{u} ≌ Sheaf (topology X) AddCommGrpCat.{u} :=
  PullbackFactory.AdditiveSheafification.comparison
    (AtlasInput.scheme X) (AtlasInput.map X) (AtlasInput.locallySurjective X)

/-- Restriction of module sheaves to the affine atlas charts, at the original coefficient universe. -/
def restriction : Modules X ⥤ SheafOfModules.{u} (structureSheaf X) :=
  SheafOfModules.pushforward (F := inclusion X) (𝟙 (structureSheaf X))

private def additiveExtension (M : SheafOfModules.{u} (structureSheaf X)) :
    Sheaf (smallEtaleTopology X) AddCommGrpCat.{u} :=
  (additiveComparison X).inverse.obj ((SheafOfModules.toSheaf (structureSheaf X)).obj M)

private def chartIso (M : SheafOfModules.{u} (structureSheaf X)) :
    ((inclusion X).sheafPushforwardContinuous AddCommGrpCat.{u} (topology X)
      (smallEtaleTopology X)).obj (additiveExtension X M) ≅
      (SheafOfModules.toSheaf (structureSheaf X)).obj M :=
  (additiveComparison X).counitIso.app _

private def chartEquiv (M : SheafOfModules.{u} (structureSheaf X)) (V : (Site X)ᵒᵖ) :
    (additiveExtension X M).obj.obj ((inclusion X).op.obj V) ≃+ M.val.obj V :=
  (((sheafToPresheaf (topology X) AddCommGrpCat.{u}).mapIso (chartIso X M)).app V).addCommGroupIsoToAddEquiv

private def scalarsAndSections (M : SheafOfModules.{u} (structureSheaf X)) :
    (smallEtaleSite X)ᵒᵖ ⥤ Type u where
  obj V := (AlgebraicSpace.structureSheaf X).obj.obj V × (additiveExtension X M).obj.obj V
  map f := ↾fun p ↦ ((AlgebraicSpace.structureSheaf X).obj.map f p.1,
    (additiveExtension X M).obj.map f p.2)
  map_id V := by
    apply ConcreteCategory.hom_ext
    intro p
    exact Prod.ext
      (ConcreteCategory.congr_hom ((AlgebraicSpace.structureSheaf X).obj.map_id V) p.1)
      (ConcreteCategory.congr_hom ((additiveExtension X M).obj.map_id V) p.2)
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro p
    exact Prod.ext
      (ConcreteCategory.congr_hom ((AlgebraicSpace.structureSheaf X).obj.map_comp f g) p.1)
      (ConcreteCategory.congr_hom ((additiveExtension X M).obj.map_comp f g) p.2)

private def restrictedSmul (M : SheafOfModules.{u} (structureSheaf X)) :
    (inclusion X).op ⋙ scalarsAndSections X M ⟶
      (inclusion X).op ⋙ (additiveExtension X M).obj ⋙ forget AddCommGrpCat.{u} where
  app V := ↾fun p ↦ (chartEquiv X M V).symm
    ((show (structureSheaf X).obj.obj V from p.1) • (show M.val.obj V from (chartEquiv X M V) p.2))
  naturality V W f := by
    ext p
    have hi := ConcreteCategory.congr_hom ((chartIso X M).inv.hom.naturality f)
      ((show (structureSheaf X).obj.obj V from p.1) • (show M.val.obj V from (chartEquiv X M V) p.2))
    have hh := ConcreteCategory.congr_hom ((chartIso X M).hom.hom.naturality f) p.2
    change (chartEquiv X M W).symm
      ((show (structureSheaf X).obj.obj W from
        (AlgebraicSpace.structureSheaf X).obj.map ((inclusion X).op.map f) p.1) •
        (chartEquiv X M W) ((additiveExtension X M).obj.map ((inclusion X).op.map f) p.2)) =
      (additiveExtension X M).obj.map ((inclusion X).op.map f)
        ((chartEquiv X M V).symm ((show (structureSheaf X).obj.obj V from p.1) • (show M.val.obj V from
          (chartEquiv X M V) p.2)))
    calc
      _ = (chartEquiv X M W).symm
          ((show (structureSheaf X).obj.obj W from
        (AlgebraicSpace.structureSheaf X).obj.map ((inclusion X).op.map f) p.1) •
            (show M.val.obj W from M.val.map f ((chartEquiv X M V) p.2))) :=
        congrArg (fun z ↦ (chartEquiv X M W).symm
          ((show (structureSheaf X).obj.obj W from
            (AlgebraicSpace.structureSheaf X).obj.map ((inclusion X).op.map f) p.1) • z)) hh
      _ = _ := (congrArg (fun z ↦ (chartEquiv X M W).symm z)
        (M.val.map_smul f (show (structureSheaf X).obj.obj V from p.1) ((chartEquiv X M V) p.2))).symm.trans hi

private def scalarAction (M : SheafOfModules.{u} (structureSheaf X)) :
    scalarsAndSections X M ⟶ (additiveExtension X M).obj ⋙ forget AddCommGrpCat.{u} :=
  Functor.IsCoverDense.restrictHomEquivHom
    (G := inclusion X)
    (ℱ' := (sheafCompose (smallEtaleTopology X) (forget AddCommGrpCat.{u})).obj
      (additiveExtension X M)) (restrictedSmul X M)

private def smulAt (M : SheafOfModules.{u} (structureSheaf X))
    (V : (smallEtaleSite X)ᵒᵖ) (r : (AlgebraicSpace.structureSheaf X).obj.obj V)
    (m : (additiveExtension X M).obj.obj V) : (additiveExtension X M).obj.obj V :=
  (scalarAction X M).app V (r, m)

private theorem smulAt_chart (M : SheafOfModules.{u} (structureSheaf X))
    (V : (Site X)ᵒᵖ) (r : (structureSheaf X).obj.obj V)
    (m : (additiveExtension X M).obj.obj ((inclusion X).op.obj V)) :
    smulAt X M ((inclusion X).op.obj V) r m =
      (chartEquiv X M V).symm (r • (show M.val.obj V from (chartEquiv X M V) m)) := by
  have h := congrArg (fun α ↦ α.app V)
    ((Functor.IsCoverDense.restrictHomEquivHom (G := inclusion X)
      (ℱ' := (sheafCompose (smallEtaleTopology X) (forget AddCommGrpCat.{u})).obj
        (additiveExtension X M))).symm_apply_apply (restrictedSmul X M))
  exact congrArg (fun α ↦ α (r, m)) h

private theorem smulAt_restrict (M : SheafOfModules.{u} (structureSheaf X))
    {V W : (smallEtaleSite X)ᵒᵖ} (f : V ⟶ W)
    (r : (AlgebraicSpace.structureSheaf X).obj.obj V)
    (m : (additiveExtension X M).obj.obj V) :
    (additiveExtension X M).obj.map f (smulAt X M V r m) =
      smulAt X M W ((AlgebraicSpace.structureSheaf X).obj.map f r)
        ((additiveExtension X M).obj.map f m) :=
  (congrArg (fun α ↦ α (r, m)) ((scalarAction X M).naturality f)).symm

private theorem section_ext (M : SheafOfModules.{u} (structureSheaf X))
    (V : (smallEtaleSite X)ᵒᵖ) {m n : (additiveExtension X M).obj.obj V}
    (h : ∀ (W : Site X) (f : (inclusion X).obj W ⟶ V.unop),
      (additiveExtension X M).obj.map f.op m = (additiveExtension X M).obj.map f.op n) : m = n :=
  Functor.IsCoverDense.ext (inclusion X)
    ((sheafCompose (smallEtaleTopology X) (forget AddCommGrpCat.{u})).obj
      (additiveExtension X M)) V.unop (fun W f ↦ h W f)

@[reducible] private def sectionModule (M : SheafOfModules.{u} (structureSheaf X))
    (V : (smallEtaleSite X)ᵒᵖ) :
    Module ((AlgebraicSpace.structureSheaf X).obj.obj V) ((additiveExtension X M).obj.obj V) where
  smul := smulAt X M V
  one_smul m := by
    change smulAt X M V 1 m = m
    apply section_ext X M V
    intro W f
    erw [smulAt_restrict, map_one, smulAt_chart]
    erw [one_smul, AddEquiv.symm_apply_apply]
  mul_smul r s m := by
    change smulAt X M V (r * s) m = smulAt X M V r (smulAt X M V s m)
    apply section_ext X M V
    intro W f
    erw [smulAt_restrict, smulAt_restrict, smulAt_restrict, map_mul,
      smulAt_chart, smulAt_chart, smulAt_chart]
    erw [AddEquiv.apply_symm_apply, mul_smul]
  smul_zero r := by
    change smulAt X M V r 0 = 0
    apply section_ext X M V
    intro W f
    erw [smulAt_restrict, map_zero, smulAt_chart]
    erw [map_zero, smul_zero, map_zero]
    rfl
  smul_add r m n := by
    change smulAt X M V r (m + n) = smulAt X M V r m + smulAt X M V r n
    apply section_ext X M V
    intro W f
    erw [smulAt_restrict, map_add, map_add, smulAt_restrict, smulAt_restrict,
      smulAt_chart, smulAt_chart, smulAt_chart]
    erw [map_add, smul_add, map_add]
    rfl
  add_smul r s m := by
    change smulAt X M V (r + s) m = smulAt X M V r m + smulAt X M V s m
    apply section_ext X M V
    intro W f
    erw [smulAt_restrict, map_add, map_add, smulAt_restrict, smulAt_restrict,
      smulAt_chart, smulAt_chart, smulAt_chart]
    have h := (M.val.obj (op W)).isModule.add_smul
      ((AlgebraicSpace.structureSheaf X).obj.map f.op r)
      ((AlgebraicSpace.structureSheaf X).obj.map f.op s)
      ((chartEquiv X M (op W)) ((additiveExtension X M).obj.map f.op m))
    erw [h, (chartEquiv X M (op W)).symm.map_add]
    rfl
  zero_smul m := by
    change smulAt X M V 0 m = 0
    apply section_ext X M V
    intro W f
    erw [smulAt_restrict, map_zero, smulAt_chart]
    erw [zero_smul, map_zero, map_zero]
    rfl

private def extensionPresheaf (M : SheafOfModules.{u} (structureSheaf X)) :
    PresheafOfModules.{u} (AlgebraicSpace.structureSheaf X).obj where
  obj V := @ModuleCat.of _ _ ((additiveExtension X M).obj.obj V) _ (sectionModule X M V)
  map {V W} f := by
    -- Local instance justification (defeq pin): sectionModule X M V pins the source to the scalar action explicitly constructed from the atlas module M for this linear restriction map.
    letI := sectionModule X M V
    -- Local instance justification (defeq pin): sectionModule X M W pins the target to the same specified extension construction before scalar restriction for this linear map.
    letI := sectionModule X M W
    -- Local instance justification (defeq pin): Module.compHom views the target over the source ring through the displayed structure-sheaf restriction map when constructing this linear restriction map.
    letI := Module.compHom ((additiveExtension X M).obj.obj W)
      ((AlgebraicSpace.structureSheaf X).obj.map f).hom
    exact ModuleCat.ofHom
      { toFun := (additiveExtension X M).obj.map f
        map_add' := ((additiveExtension X M).obj.map f).hom.map_add
        map_smul' := smulAt_restrict X M f }
  map_id V := by
    apply ConcreteCategory.hom_ext
    intro m
    exact ConcreteCategory.congr_hom ((additiveExtension X M).obj.map_id V) m
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro m
    exact ConcreteCategory.congr_hom ((additiveExtension X M).obj.map_comp f g) m

set_option backward.privateInPublic true in
/-- Right Kan extension of an atlas module sheaf, with the uniquely extended structure-sheaf action. -/
def extensionObj (M : SheafOfModules.{u} (structureSheaf X)) : Modules X where
  val := extensionPresheaf X M
  isSheaf := (additiveExtension X M).property

private def additiveExtensionMap {M N : SheafOfModules.{u} (structureSheaf X)} (f : M ⟶ N) :
    additiveExtension X M ⟶ additiveExtension X N :=
  (additiveComparison X).inverse.map ((SheafOfModules.toSheaf (structureSheaf X)).map f)

private theorem extensionMap_smul {M N : SheafOfModules.{u} (structureSheaf X)} (f : M ⟶ N)
    (V : (smallEtaleSite X)ᵒᵖ) (r : (AlgebraicSpace.structureSheaf X).obj.obj V)
    (m : (additiveExtension X M).obj.obj V) :
    (additiveExtensionMap X f).hom.app V (smulAt X M V r m) =
      smulAt X N V r ((additiveExtensionMap X f).hom.app V m) := by
  apply section_ext X N V
  intro W g
  have h := ConcreteCategory.congr_hom ((additiveExtensionMap X f).hom.naturality g.op)
    (smulAt X M V r m)
  change (additiveExtensionMap X f).hom.app ((inclusion X).op.obj (op W))
      ((additiveExtension X M).obj.map g.op (smulAt X M V r m)) =
    (additiveExtension X N).obj.map g.op
      ((additiveExtensionMap X f).hom.app V (smulAt X M V r m)) at h
  have hm := ConcreteCategory.congr_hom ((additiveExtensionMap X f).hom.naturality g.op) m
  change (additiveExtensionMap X f).hom.app ((inclusion X).op.obj (op W))
      ((additiveExtension X M).obj.map g.op m) =
    (additiveExtension X N).obj.map g.op ((additiveExtensionMap X f).hom.app V m) at hm
  erw [← h, smulAt_restrict, smulAt_restrict, ← hm, smulAt_chart, smulAt_chart]
  have hc := ConcreteCategory.congr_hom
    (congrArg (fun α ↦ α.hom.app (op W))
      ((additiveComparison X).counitIso.hom.naturality
        ((SheafOfModules.toSheaf (structureSheaf X)).map f)))
  change ∀ m, (chartEquiv X N (op W))
      ((additiveExtensionMap X f).hom.app ((inclusion X).op.obj (op W)) m) =
      f.val.app (op W) ((chartEquiv X M (op W)) m) at hc
  apply (chartEquiv X N (op W)).injective
  erw [hc, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, hc]
  exact (f.val.app (op W)).hom.map_smul _ _

set_option backward.privateInPublic true in
/-- Right Kan extension of atlas module sheaves and their linear morphisms. -/
def extension : SheafOfModules.{u} (structureSheaf X) ⥤ Modules X where
  obj := extensionObj X
  map f := ⟨PresheafOfModules.homMk (additiveExtensionMap X f).hom (extensionMap_smul X f)⟩
  map_id M := by
    ext V m
    have h := (additiveComparison X).inverse.map_id
      ((SheafOfModules.toSheaf (structureSheaf X)).obj M)
    have hv := congrArg (fun α ↦ α.hom.app V) h
    exact ConcreteCategory.congr_hom hv m
  map_comp f g := by
    ext V m
    have h := (additiveComparison X).inverse.map_comp
      ((SheafOfModules.toSheaf (structureSheaf X)).map f)
      ((SheafOfModules.toSheaf (structureSheaf X)).map g)
    have hv := congrArg (fun α ↦ α.hom.app V) h
    exact ConcreteCategory.congr_hom hv m

set_option backward.isDefEq.respectTransparency false

private theorem linear_on_charts {M N : Modules X}
    (f : (SheafOfModules.toSheaf (AlgebraicSpace.structureSheaf X)).obj M ⟶
      (SheafOfModules.toSheaf (AlgebraicSpace.structureSheaf X)).obj N)
    (h : ∀ (V : (Site X)ᵒᵖ) (r : (AlgebraicSpace.structureSheaf X).obj.obj ((inclusion X).op.obj V))
      (m : M.val.obj ((inclusion X).op.obj V)),
      f.hom.app ((inclusion X).op.obj V) (r • m) =
        r • (show N.val.obj ((inclusion X).op.obj V) from
          f.hom.app ((inclusion X).op.obj V) m))
    (V : (smallEtaleSite X)ᵒᵖ) (r : (AlgebraicSpace.structureSheaf X).obj.obj V)
    (m : M.val.obj V) :
    f.hom.app V (r • m) = r • (show N.val.obj V from f.hom.app V m) := by
  apply Functor.IsCoverDense.ext (inclusion X)
    ((sheafCompose (smallEtaleTopology X) (forget AddCommGrpCat.{u})).obj
      ((SheafOfModules.toSheaf (AlgebraicSpace.structureSheaf X)).obj N)) V.unop
  intro W g
  have hf := ConcreteCategory.congr_hom (f.hom.naturality g.op)
  change ∀ z, f.hom.app (op ((inclusion X).obj W)) (M.val.map g.op z) =
    N.val.map g.op (f.hom.app V z) at hf
  erw [← hf, N.val.map_smul, M.val.map_smul, h, hf]
  all_goals rfl

private def counitHom : extension X ⋙ restriction X ⟶ 𝟭 (SheafOfModules.{u} (structureSheaf X)) where
  app M := ⟨PresheafOfModules.homMk (chartIso X M).hom.hom (by
    intro V r m
    change (chartEquiv X M V) (smulAt X M ((inclusion X).op.obj V) r m) = _
    erw [smulAt_chart, AddEquiv.apply_symm_apply]
    all_goals rfl)⟩
  naturality M N f := by
    ext V m
    have hv := congrArg (fun α ↦ α.hom.app V)
        ((additiveComparison X).counitIso.hom.naturality
          ((SheafOfModules.toSheaf (structureSheaf X)).map f))
    exact ConcreteCategory.congr_hom hv m

private def counitInv : 𝟭 (SheafOfModules.{u} (structureSheaf X)) ⟶ extension X ⋙ restriction X where
  app M := ⟨PresheafOfModules.homMk (chartIso X M).inv.hom (by
    intro V r m
    change (chartEquiv X M V).symm (r • m) =
      smulAt X M ((inclusion X).op.obj V) r ((chartEquiv X M V).symm m)
    erw [smulAt_chart, AddEquiv.apply_symm_apply]
    all_goals rfl)⟩
  naturality M N f := by
    ext V m
    have hv := congrArg (fun α ↦ α.hom.app V)
        ((additiveComparison X).counitIso.inv.naturality
          ((SheafOfModules.toSheaf (structureSheaf X)).map f))
    exact ConcreteCategory.congr_hom hv m

private def liftAdditive {M N : Modules X}
    (f : (restriction X).obj M ⟶ (restriction X).obj N) :
    (SheafOfModules.toSheaf (AlgebraicSpace.structureSheaf X)).obj M ⟶
      (SheafOfModules.toSheaf (AlgebraicSpace.structureSheaf X)).obj N :=
  ⟨Functor.IsCoverDense.restrictHomEquivHom (G := inclusion X)
    (ℱ := M.val.presheaf)
    (ℱ' := (SheafOfModules.toSheaf (AlgebraicSpace.structureSheaf X)).obj N)
    ((PresheafOfModules.toPresheaf (structureSheaf X).obj).map f.val)⟩

private theorem liftAdditive_chart {M N : Modules X}
    (f : (restriction X).obj M ⟶ (restriction X).obj N) (V : (Site X)ᵒᵖ)
    (m : M.val.obj ((inclusion X).op.obj V)) :
    (liftAdditive X f).hom.app ((inclusion X).op.obj V) m = f.val.app V m := by
  have h := congrArg (fun α ↦ α.app V)
    ((Functor.IsCoverDense.restrictHomEquivHom (G := inclusion X)
      (ℱ := M.val.presheaf)
      (ℱ' := (SheafOfModules.toSheaf (AlgebraicSpace.structureSheaf X)).obj N)).symm_apply_apply
      ((PresheafOfModules.toPresheaf (structureSheaf X).obj).map f.val))
  exact ConcreteCategory.congr_hom h m

private def liftMap {M N : Modules X}
    (f : (restriction X).obj M ⟶ (restriction X).obj N) : M ⟶ N :=
  ⟨PresheafOfModules.homMk (liftAdditive X f).hom (linear_on_charts X (liftAdditive X f) (by
    intro V r m
    erw [liftAdditive_chart, liftAdditive_chart]
    exact (f.val.app V).hom.map_smul r m))⟩

private theorem liftMap_fac {M N : Modules X}
    (f : (restriction X).obj M ⟶ (restriction X).obj N) :
    (restriction X).map (liftMap X f) = f := by
  ext V m
  exact liftAdditive_chart X f V m

private theorem restriction_injective {M N : Modules X} (f g : M ⟶ N)
    (h : (restriction X).map f = (restriction X).map g) : f = g := by
  ext V m
  apply Functor.IsCoverDense.ext (inclusion X)
    ((sheafCompose (smallEtaleTopology X) (forget AddCommGrpCat.{u})).obj
      ((SheafOfModules.toSheaf (AlgebraicSpace.structureSheaf X)).obj N)) V.unop
  intro W a
  have hf := CategoryTheory.congr_fun (f.val.naturality a.op) m
  have hg := CategoryTheory.congr_fun (g.val.naturality a.op) m
  change f.val.app (op ((inclusion X).obj W)) (M.val.map a.op m) = N.val.map a.op (f.val.app V m) at hf
  change g.val.app (op ((inclusion X).obj W)) (M.val.map a.op m) = N.val.map a.op (g.val.app V m) at hg
  have hv := congrArg (fun α ↦ α.val.app (op W)) h
  exact hf.symm.trans ((ConcreteCategory.congr_hom hv _).trans hg)

private def unitHom : 𝟭 (Modules X) ⟶ restriction X ⋙ extension X where
  app M := liftMap X ((counitInv X).app ((restriction X).obj M))
  naturality M N f := by
    apply restriction_injective X
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
      liftMap_fac, liftMap_fac]
    exact (counitInv X).naturality ((restriction X).map f)

private def unitInv : restriction X ⋙ extension X ⟶ 𝟭 (Modules X) where
  app M := liftMap X ((counitHom X).app ((restriction X).obj M))
  naturality M N f := by
    apply restriction_injective X
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
      liftMap_fac, liftMap_fac]
    exact (counitHom X).naturality ((restriction X).map f)

/-- The unit maps for restriction to the atlas are mutually inverse. -/
theorem unit_hom_inv_id : unitHom X ≫ unitInv X = 𝟙 _ := sorry

/-- The inverse unit followed by the unit is the identity. -/
theorem unit_inv_hom_id : unitInv X ≫ unitHom X = 𝟙 _ := sorry

/-- The counit maps for restriction to the atlas are mutually inverse. -/
theorem counit_hom_inv_id : counitHom X ≫ counitInv X = 𝟙 _ := sorry

/-- The inverse counit followed by the counit is the identity. -/
theorem counit_inv_hom_id : counitInv X ≫ counitHom X = 𝟙 _ := sorry

/-- The unit and counit of atlas restriction satisfy the triangle identity. -/
theorem functor_unitIso_comp (M : Modules X) :
    (restriction X).map ((unitHom X).app M) ≫
      (counitHom X).app ((restriction X).obj M) = 𝟙 _ := sorry

/-- Restriction to the affine atlas is an equivalence on module sheaves. -/
def equivalence : Modules X ≌ SheafOfModules.{u} (structureSheaf X) where
  functor := restriction X
  inverse := extension X
  unitIso := ⟨unitHom X, unitInv X, unit_hom_inv_id X, unit_inv_hom_id X⟩
  counitIso := ⟨counitHom X, counitInv X, counit_hom_inv_id X, counit_inv_hom_id X⟩
  functor_unitIso_comp := functor_unitIso_comp X

/-- Atlas restriction preserves addition of module morphisms. -/
instance restriction_additive : (restriction X).Additive where
  map_add := by
    intro M N f g
    ext V m
    rfl

/-- The specified extension of module sheaves preserves addition. -/
instance extension_additive : (extension X).Additive :=
  @Equivalence.inverse_additive _ _ _ _ _ _ (equivalence X) (restriction_additive X)

/-- Atlas restriction has the specified extension as its quasi-inverse. -/
instance restriction_isEquivalence : (restriction X).IsEquivalence :=
  (equivalence X).isEquivalence_functor

/-- Atlas extension has restriction as its quasi-inverse. -/
instance extension_isEquivalence : (extension X).IsEquivalence :=
  (equivalence X).isEquivalence_inverse

/-- The standard derived category of module sheaves on the small atlas. -/
instance modulesHasDerivedCategory : HasDerivedCategory (SheafOfModules.{u} (structureSheaf X)) :=
  HasDerivedCategory.standard _

/-- The equivalence of derived module categories induced by exact restriction and extension. -/
def derivedEquivalence : ModuleDerived X ≌ DerivedCategory (SheafOfModules.{u} (structureSheaf X)) :=
  let e := (equivalence X).mapHomologicalComplex (.up ℤ)
  Localization.equivalence
    DerivedCategory.Q (HomologicalComplex.quasiIso (Modules X) (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso (SheafOfModules.{u} (structureSheaf X)) (.up ℤ))
    ((restriction X).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) (restriction X).mapDerivedCategory
    ((extension X).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) (extension X).mapDerivedCategory
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft e.functor (extension X).mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight e.unitIso.symm DerivedCategory.Q ≪≫ Functor.leftUnitor _)
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft e.inverse (restriction X).mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight e.counitIso DerivedCategory.Q ≪≫ Functor.leftUnitor _)

/-- The commutative structure sheaf on the affine atlas, with coefficients in the original universe. -/
def commStructureSheaf : Sheaf (topology X) CommRingCat.{u} :=
  ((inclusion X).sheafPushforwardContinuous CommRingCat.{u} (topology X)
    (smallEtaleTopology X)).obj (AlgebraicSpace.commStructureSheaf X)

/-- Forgetting commutativity of the atlas structure sheaf gives its ring-valued structure sheaf. -/
theorem commStructureSheaf_forget :
    (sheafCompose (topology X) (forget₂ CommRingCat.{u} RingCat.{u})).obj
      (commStructureSheaf X) = structureSheaf X := rfl

end AlgebraicGeometry.AlgebraicSpace.Modules.Atlas
