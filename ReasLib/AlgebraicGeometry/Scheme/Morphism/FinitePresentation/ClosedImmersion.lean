/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedImmersion
import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.KernelIdeal
import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.LocalProperties.Covers
import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Pullback.LocalGeneration
import ReasLib.AlgebraicGeometry.LocallyRingedSpace.ClosedImmersion.Scheme
import ReasLib.AlgebraicGeometry.RingedSite.Basic
import ReasLib.AlgebraicGeometry.RingedSite.Module.Intrinsic
import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpensRingedSite
import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite presentation of closed immersions

A closed immersion is locally of finite presentation exactly when its kernel ideal sheaf is of
finite type.
-/

@[expose] public section

open CategoryTheory Limits Opposite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

private lemma denseOver {T : Type u} [TopologicalSpace T]
    (U : TopologicalSpace.Opens T) :
    U.overEquivalence.functor.IsDenseSubsite
      ((Opens.grothendieckTopology T).over U)
      (Opens.grothendieckTopology U) := by
  infer_instance

private lemma continuousOver {T : Type u} [TopologicalSpace T]
    (U : TopologicalSpace.Opens T) :
    U.overEquivalence.functor.IsContinuous
      ((Opens.grothendieckTopology T).over U)
      (Opens.grothendieckTopology U) := by
  letI := denseOver U
  infer_instance

private lemma representablyFlatOver {T : Type u} [TopologicalSpace T]
    (U : TopologicalSpace.Opens T) :
    RepresentablyFlat U.overEquivalence.functor := by
  infer_instance

private lemma typePullbackEquivalenceOver {T : Type u} [TopologicalSpace T]
    (U : TopologicalSpace.Opens T) :
    (U.overEquivalence.functor.sheafPullback (Type u)
      ((Opens.grothendieckTopology T).over U)
      (Opens.grothendieckTopology U)).IsEquivalence := by
  letI := denseOver U
  letI := continuousOver U
  letI : (U.overEquivalence.functor.sheafPushforwardContinuous (Type u)
      ((Opens.grothendieckTopology T).over U)
      (Opens.grothendieckTopology U)).IsEquivalence := inferInstance
  exact (U.overEquivalence.functor.sheafAdjunctionContinuous (Type u)
    ((Opens.grothendieckTopology T).over U)
    (Opens.grothendieckTopology U)).isEquivalence_left_of_isEquivalence_right

private lemma structureMapIsoOver {T : Type u} [TopologicalSpace T]
    (U : TopologicalSpace.Opens T)
    (R : Sheaf (Opens.grothendieckTopology T) CommRingCat.{u}) :
    IsIso ((sheafCompose ((Opens.grothendieckTopology T).over U)
      (forget₂ CommRingCat RingCat)).map
        (show ((Opens.grothendieckTopology T).overPullback CommRingCat U).obj R ⟶
            (TopologicalSpace.Opens.sheafRestrict
                (X := TopCat.of T) (C := CommRingCat) U ⋙
              (TopologicalSpace.Opens.sheafEquivOver
                (X := TopCat.of T) (A := CommRingCat) U).inverse).obj R from
          ((TopologicalSpace.Opens.sheafRestrictSheafEquivOver
            (X := TopCat.of T) (A := CommRingCat) U).app R).inv)) := by
  letI : IsIso ((TopologicalSpace.Opens.sheafRestrictSheafEquivOver
      (X := TopCat.of T) (A := CommRingCat) U).app R).inv := inferInstance
  infer_instance

private noncomputable def openLocalizationHom {X : Scheme.{u}} (U : X.Opens) :
    RingedSite.Hom
      (RingedSite.ofCommRingSheaf (Opens.grothendieckTopology U.toScheme)
        (U.sheafRestrict.obj X.sheaf))
      (RingedSite.ofCommRingSheaf ((Opens.grothendieckTopology X).over U)
        (X.sheaf.over U)) := by
  letI : U.overEquivalence.functor.IsDenseSubsite
      ((Opens.grothendieckTopology X).over U)
      (Opens.grothendieckTopology U) := denseOver U
  letI : U.overEquivalence.functor.IsContinuous
      ((Opens.grothendieckTopology X).over U)
      (Opens.grothendieckTopology U) := continuousOver U
  letI : RepresentablyFlat U.overEquivalence.functor :=
    representablyFlatOver U
  refine
    { base := U.overEquivalence.functor
      isMorphismOfSites := { }
      structureSheafMap := ?_ }
  exact (sheafCompose ((Opens.grothendieckTopology X).over U)
    (forget₂ CommRingCat RingCat)).map
      (U.sheafRestrictSheafEquivOver.app X.sheaf).inv

private lemma openLocalizationHom_isRingedEquivalence {X : Scheme.{u}}
    (U : X.Opens) : (openLocalizationHom U).IsRingedEquivalence := by
  constructor
  · dsimp [openLocalizationHom]
    exact typePullbackEquivalenceOver U
  · dsimp [openLocalizationHom]
    exact structureMapIsoOver U X.sheaf

private lemma overEquiv_isFiniteType_iff {X : Scheme.{u}} (U : X.Opens)
    (M : SheafOfModules (X.ringCatSheaf.over U)) :
    ((Scheme.Modules.overEquiv U).functor.obj M).IsFiniteType ↔
      M.IsFiniteType := by
  let f := openLocalizationHom U
  letI : f.IsRingedEquivalence := openLocalizationHom_isRingedEquivalence U
  let E : f.modulePullback.obj M ≅
      (Scheme.Modules.overEquiv U).functor.obj M := by
    exact (Adjunction.leftAdjointUniq
      (RingedSite.Hom.modulePullbackPushforwardAdjunction f)
      (Scheme.Modules.overEquiv U).toAdjunction).app M
  constructor
  · intro h
    have h' : (f.modulePullback.obj M).IsFiniteType :=
      @SheafOfModules.isFiniteType_of_iso _ _ _ _ _ _ _ _ E.symm h
    exact (RingedSite.Hom.pullback_isFiniteType_iff f M).mp h'
  · intro h
    have h' : (f.modulePullback.obj M).IsFiniteType :=
      (RingedSite.Hom.pullback_isFiniteType_iff f M).mpr h
    exact @SheafOfModules.isFiniteType_of_iso _ _ _ _ _ _ _ _ E h'

private lemma restrict_eq {X Z : Scheme.{u}} (i : Z ⟶ X) (U : X.Opens) :
    (i ∣_ U).toLRSHom = i.toLRSHom.restrictToPreimageOpen U := by
  apply LocallyRingedSpace.Hom.restrictToPreimageOpen.unique
  change (i ∣_ U).toLRSHom ≫ U.ι.toLRSHom =
    (i ⁻¹ᵁ U).ι.toLRSHom ≫ i.toLRSHom
  exact congrArg Scheme.Hom.toLRSHom (morphismRestrict_ι i U)

private lemma fromSpec_ΓIsoTop {X : Scheme.{u}} (U : X.affineOpens) :
    let g := U.2.fromSpec
    let hImage : g ''ᵁ (⊤ : (Spec Γ(X, U)).Opens) = U.1 :=
      g.image_top_eq_opensRange.trans U.2.opensRange_fromSpec
    (g.appIso ⊤).symm ≪≫ X.presheaf.mapIso (eqToIso hImage).symm.op =
      Scheme.ΓSpecIso Γ(X, U) := by
  dsimp only
  let g := U.2.fromSpec
  let hImage : g ''ᵁ (⊤ : (Spec Γ(X, U)).Opens) = U.1 :=
    g.image_top_eq_opensRange.trans U.2.opensRange_fromSpec
  apply Iso.ext
  rw [← cancel_mono (Scheme.ΓSpecIso Γ(X, U)).inv]
  simp only [Iso.trans_hom, Category.assoc, Iso.hom_inv_id]
  let q := (Spec Γ(X, U)).presheaf.map
    (eqToHom U.2.fromSpec_preimage_self).op
  rw [← cancel_mono q, Category.id_comp]
  simp only [Category.assoc]
  rw [← U.2.fromSpec_app_self]
  simp only [Iso.symm_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.inv]
  change (g.appIso ⊤).inv ≫ X.presheaf.map (eqToHom hImage.symm).op ≫
    g.app U.1 = q
  rw [g.naturality]
  rw [Scheme.Hom.appIso_inv_app_assoc]
  rw [← Functor.map_comp]
  rfl

private noncomputable def chartSectionsIso {X : Scheme.{u}} (M : X.Modules)
    (U : X.affineOpens) :
    (moduleSpecΓFunctor (R := Γ(X, U))).obj
        ((Scheme.Modules.restrictFunctor U.2.fromSpec).obj M) ≅
      ModuleCat.of Γ(X, U) Γ(M, U.1) := by
  let g := U.2.fromSpec
  let hImage : g ''ᵁ (⊤ : (Spec Γ(X, U)).Opens) = U.1 :=
    g.image_top_eq_opensRange.trans U.2.opensRange_fromSpec
  let eAdd :
      (forget₂ (ModuleCat Γ(X, U)) AddCommGrpCat).obj
          ((moduleSpecΓFunctor (R := Γ(X, U))).obj
            ((Scheme.Modules.restrictFunctor g).obj M)) ≅
        (forget₂ (ModuleCat Γ(X, U)) AddCommGrpCat).obj
          (ModuleCat.of Γ(X, U) Γ(M, U.1)) :=
    M.restrictAppIso g ⊤ ≪≫
      M.presheaf.mapIso (eqToIso hImage).symm.op
  exact ModuleCat.isoMk eAdd (by
    intro r
    ext x
    let N := (Scheme.Modules.restrictFunctor g).obj M
    let xN : Γ(N, (⊤ : (Spec Γ(X, U)).Opens)) := x
    change r • (M.presheaf.map (eqToHom hImage.symm).op
      ((M.restrictAppIso g ⊤).hom xN)) =
      M.presheaf.map (eqToHom hImage.symm).op
        ((M.restrictAppIso g ⊤).hom
          (((Scheme.ΓSpecIso Γ(X, U)).inv.hom r) • xN))
    rw [Scheme.Modules.smul_restrictAppIso_hom_apply]
    rw [M.map_smul]
    have hRing := congrArg Iso.hom (fromSpec_ΓIsoTop U)
    have hr := congrArg
      (fun f => f.hom ((Scheme.ΓSpecIso Γ(X, U)).inv.hom r)) hRing
    simp only [Iso.trans_hom, CommRingCat.hom_comp,
      Iso.inv_hom_id_apply] at hr
    exact congrArg
      (fun s : Γ(X, U) => s •
        (M.presheaf.map (eqToHom hImage.symm).op
          ((M.restrictAppIso g ⊤).hom xN))) hr.symm)

private noncomputable def chartIdealSectionsIso {X Z : Scheme.{u}}
    (i : Z ⟶ X) (U : X.affineOpens) :
    (moduleSpecΓFunctor (R := Γ(X, U))).obj
        ((Scheme.Modules.restrictFunctor U.2.fromSpec).obj
          (RingedSpace.Hom.idealSheaf i.toShHom)) ≅
      ModuleCat.of Γ(X, U)
        (LocallyRingedSpace.Hom.affineOpenKernelIdeal i.toLRSHom U) :=
  chartSectionsIso (RingedSpace.Hom.idealSheaf i.toShHom) U ≪≫
    SheafOfModules.RingedSite.KernelIdeal.sectionsIso
      (RingedSpace.Hom.commRingSheafPushforwardMap i.toShHom) (op U.1)

private lemma spec_isFiniteType_iff_module_finite {R : CommRingCat.{u}}
    (N : (Spec R).Modules) [N.IsQuasicoherent] :
    N.IsFiniteType ↔ Module.Finite R ((moduleSpecΓFunctor (R := R)).obj N) := by
  let hIso : IsIso (Scheme.Modules.fromTildeΓ (R := R) N) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent N
  let e : tilde ((moduleSpecΓFunctor (R := R)).obj N) ≅ N :=
    @asIso _ _ _ _ (Scheme.Modules.fromTildeΓ (R := R) N) hIso
  constructor
  · intro h
    letI : N.IsFiniteType := h
    have hTilde : (tilde ((moduleSpecΓFunctor (R := R)).obj N)).IsFiniteType :=
      SheafOfModules.isFiniteType_of_iso e.symm
    exact (Scheme.Modules.tilde_isFiniteType_iff_module_finite _).mp hTilde
  · intro h
    letI : Module.Finite R ((moduleSpecΓFunctor (R := R)).obj N) := h
    have hTilde : (tilde ((moduleSpecΓFunctor (R := R)).obj N)).IsFiniteType :=
      (Scheme.Modules.tilde_isFiniteType_iff_module_finite _).mpr inferInstance
    letI : (tilde ((moduleSpecΓFunctor (R := R)).obj N)).IsFiniteType := hTilde
    exact SheafOfModules.isFiniteType_of_iso e

private lemma chartIdeal_isFiniteType_iff_fg {X Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (U : X.affineOpens) :
    let N := (Scheme.Modules.restrictFunctor U.2.fromSpec).obj
      (RingedSpace.Hom.idealSheaf i.toShHom)
    N.IsFiniteType ↔
      (LocallyRingedSpace.Hom.affineOpenKernelIdeal i.toLRSHom U).FG := by
  dsimp only
  let N := (Scheme.Modules.restrictFunctor U.2.fromSpec).obj
    (RingedSpace.Hom.idealSheaf i.toShHom)
  letI : N.IsQuasicoherent := inferInstance
  calc
    N.IsFiniteType ↔
        Module.Finite Γ(X, U) ((moduleSpecΓFunctor (R := Γ(X, U))).obj N) :=
      spec_isFiniteType_iff_module_finite N
    _ ↔ Module.Finite Γ(X, U)
        (LocallyRingedSpace.Hom.affineOpenKernelIdeal i.toLRSHom U) :=
      Module.Finite.equiv_iff (chartIdealSectionsIso i U).toLinearEquiv
    _ ↔ (LocallyRingedSpace.Hom.affineOpenKernelIdeal i.toLRSHom U).FG :=
      Module.Finite.iff_fg

private lemma restrict_isFiniteType {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (M : Y.Modules) [M.IsFiniteType] :
    ((Scheme.Modules.restrictFunctor f).obj M).IsFiniteType := by
  let g := RingedSpace.opensRingedSiteHom f.toLRSHom.toShHom
  letI : g.base.Final := CategoryTheory.final_of_representablyFlat g.base
  have h : ((Scheme.Modules.pullback f).obj M).IsFiniteType := by
    change (g.modulePullback.obj M).IsFiniteType
    infer_instance
  letI : ((Scheme.Modules.pullback f).obj M).IsFiniteType := h
  exact SheafOfModules.isFiniteType_of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback f).app M).symm

private lemma restrictIso_isFiniteType_iff {X Y : Scheme.{u}} (e : X ≅ Y)
    (M : Y.Modules) :
    ((Scheme.Modules.restrictFunctor e.hom).obj M).IsFiniteType ↔
      M.IsFiniteType := by
  constructor
  · intro h
    let N := (Scheme.Modules.restrictFunctor e.hom).obj M
    letI : N.IsFiniteType := h
    have hback : ((Scheme.Modules.restrictFunctor e.inv).obj N).IsFiniteType :=
      restrict_isFiniteType e.inv N
    letI : ((Scheme.Modules.restrictFunctor e.inv).obj N).IsFiniteType := hback
    let E : (Scheme.Modules.restrictFunctor e.inv).obj N ≅ M :=
      ((Scheme.Modules.restrictFunctorComp e.inv e.hom).app M).symm ≪≫
        (Scheme.Modules.restrictFunctorCongr e.inv_hom_id).app M ≪≫
        (Scheme.Modules.restrictFunctorId (X := Y)).app M
    exact SheafOfModules.isFiniteType_of_iso E
  · intro h
    letI : M.IsFiniteType := h
    exact restrict_isFiniteType e.hom M

private lemma chartRestrict_isFiniteType_iff_openRestrict {X : Scheme.{u}}
    (M : X.Modules) (U : X.affineOpens) :
    ((Scheme.Modules.restrictFunctor U.2.fromSpec).obj M).IsFiniteType ↔
      ((Scheme.Modules.restrictFunctor U.1.ι).obj M).IsFiniteType := by
  let N := (Scheme.Modules.restrictFunctor U.1.ι).obj M
  let E : (Scheme.Modules.restrictFunctor U.2.fromSpec).obj M ≅
      (Scheme.Modules.restrictFunctor U.2.isoSpec.inv).obj N :=
    (Scheme.Modules.restrictFunctorComp U.2.isoSpec.inv U.1.ι).app M
  constructor
  · intro h
    letI : ((Scheme.Modules.restrictFunctor U.2.fromSpec).obj M).IsFiniteType := h
    have hN' : ((Scheme.Modules.restrictFunctor U.2.isoSpec.inv).obj N).IsFiniteType :=
      SheafOfModules.isFiniteType_of_iso E
    exact (restrictIso_isFiniteType_iff U.2.isoSpec.symm N).mp hN'
  · intro h
    have hN' : ((Scheme.Modules.restrictFunctor U.2.isoSpec.inv).obj N).IsFiniteType :=
      (restrictIso_isFiniteType_iff U.2.isoSpec.symm N).mpr h
    letI : ((Scheme.Modules.restrictFunctor U.2.isoSpec.inv).obj N).IsFiniteType := hN'
    exact SheafOfModules.isFiniteType_of_iso E.symm

private lemma isFiniteType_iff_of_iso {X : Scheme.{u}} {M N : X.Modules}
    (e : M ≅ N) : M.IsFiniteType ↔ N.IsFiniteType := by
  constructor
  · intro h
    exact @SheafOfModules.isFiniteType_of_iso _ _ _ _ _ _ _ _ e h
  · intro h
    exact @SheafOfModules.isFiniteType_of_iso _ _ _ _ _ _ _ _ e.symm h

private lemma over_isFiniteType_iff_restrict {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens) :
    (M.over U).IsFiniteType ↔
      ((Scheme.Modules.restrictFunctor U.ι).obj M).IsFiniteType := by
  calc
    (M.over U).IsFiniteType ↔
        ((Scheme.Modules.overEquiv U).functor.obj (M.over U)).IsFiniteType :=
      (overEquiv_isFiniteType_iff U (M.over U)).symm
    _ ↔ ((Scheme.Modules.restrictFunctor U.ι).obj M).IsFiniteType :=
      isFiniteType_iff_of_iso ((Scheme.Modules.overFunctorEquiv U).app M)

private lemma isFiniteType_iff_forall_affine {X : Scheme.{u}} (M : X.Modules) :
    M.IsFiniteType ↔
      ∀ U : X.affineOpens,
        ((Scheme.Modules.restrictFunctor U.2.fromSpec).obj M).IsFiniteType := by
  constructor
  · intro h U
    letI : M.IsFiniteType := h
    exact restrict_isFiniteType U.2.fromSpec M
  · intro h
    rw [SheafOfModules.RingedSite.IsFiniteType.iff_existsCover]
    refine ⟨X.affineOpens, fun U ↦ U.1, ?_, ?_⟩
    · rw [Opens.coversTop_iff]
      exact TopologicalSpace.IsOpenCover.mk (iSup_affineOpens_eq_top X)
    · intro U
      apply (over_isFiniteType_iff_restrict M U.1).mpr
      exact (chartRestrict_isFiniteType_iff_openRestrict M U).mp (h U)

private lemma ideal_isFiniteType_iff_forall_fg {X Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    (RingedSpace.Hom.idealSheaf i.toShHom).IsFiniteType ↔
      ∀ U : X.affineOpens,
        (LocallyRingedSpace.Hom.affineOpenKernelIdeal i.toLRSHom U).FG := by
  calc
    (RingedSpace.Hom.idealSheaf i.toShHom).IsFiniteType ↔
        ∀ U : X.affineOpens,
          ((Scheme.Modules.restrictFunctor U.2.fromSpec).obj
            (RingedSpace.Hom.idealSheaf i.toShHom)).IsFiniteType :=
      isFiniteType_iff_forall_affine _
    _ ↔ ∀ U : X.affineOpens,
        (LocallyRingedSpace.Hom.affineOpenKernelIdeal i.toLRSHom U).FG :=
      forall_congr' fun U ↦ chartIdeal_isFiniteType_iff_fg i U

private lemma quotient_lfp_iff_fg {R : Type u} [CommRing R] (I : Ideal R) :
    LocallyOfFinitePresentation
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ↔ I.FG := by
  rw [LocallyOfFinitePresentation.SpecMap_iff]
  constructor
  · intro h
    letI : Algebra.FinitePresentation R (R ⧸ I) := h
    simpa [Ideal.Quotient.mkₐ_ker] using
      (Algebra.FinitePresentation.ker_fG_of_surjective
        (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ_surjective R I))
  · intro h
    exact RingHom.FinitePresentation.of_surjective
      (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective (by simpa using h)

private lemma local_lfp_iff_fg {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (U : X.affineOpens) :
    LocallyOfFinitePresentation (i ∣_ U) ↔
      (LocallyRingedSpace.Hom.affineOpenKernelIdeal i.toLRSHom U).FG := by
  rw [← LocallyRingedSpace.Hom.AffineOpen.globalSectionsKernelIdeal_eq
    i.toLRSHom U]
  let r := LocallyRingedSpace.Hom.AffineOpen.restrictedMap i.toLRSHom U
  let q := Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.mk r.globalSectionsKernelIdeal))
  let c : ((i ⁻¹ᵁ U.1) : Scheme.{u}) ⟶ Spec (CommRingCat.of
      (Γ(X, U) ⧸ r.globalSectionsKernelIdeal)) :=
    Scheme.fullyFaithfulForgetToLocallyRingedSpace.preimage
      (LocallyRingedSpace.Hom.AffineQuotient.comparison r)
  have hg : ((i ∣_ U) ≫ U.2.isoSpec.hom).toLRSHom = r := by
    change (i ∣_ U).toLRSHom ≫
      (Scheme.forgetToLocallyRingedSpace.mapIso U.2.isoSpec).hom = _
    rw [restrict_eq]
    rfl
  letI : IsIso (LocallyRingedSpace.Hom.AffineQuotient.comparison r) :=
    LocallyRingedSpace.Hom.AffineQuotient.comparison_isIso r
  have hmap : Scheme.forgetToLocallyRingedSpace.map c =
      LocallyRingedSpace.Hom.AffineQuotient.comparison r := by
    exact Scheme.fullyFaithfulForgetToLocallyRingedSpace.map_preimage _
  letI : IsIso (Scheme.forgetToLocallyRingedSpace.map c) := by
    exact hmap.symm ▸
      LocallyRingedSpace.Hom.AffineQuotient.comparison_isIso r
  letI : IsIso c :=
    Scheme.fullyFaithfulForgetToLocallyRingedSpace.isIso_of_isIso_map c
  have hfactor : c ≫ q = (i ∣_ U) ≫ U.2.isoSpec.hom := by
    apply Scheme.forgetToLocallyRingedSpace.map_injective
    rw [Scheme.forgetToLocallyRingedSpace.map_comp,
      Scheme.forgetToLocallyRingedSpace.map_comp, hmap]
    change LocallyRingedSpace.Hom.AffineQuotient.comparison r ≫
      LocallyRingedSpace.Hom.AffineQuotient.ι r = _
    rw [LocallyRingedSpace.Hom.AffineQuotient.comparison_ι]
    exact hg.symm
  calc
    LocallyOfFinitePresentation (i ∣_ U) ↔
        LocallyOfFinitePresentation ((i ∣_ U) ≫ U.2.isoSpec.hom) :=
      (MorphismProperty.cancel_right_of_respectsIso
        @LocallyOfFinitePresentation (i ∣_ U) U.2.isoSpec.hom).symm
    _ ↔ LocallyOfFinitePresentation (c ≫ q) := by rw [hfactor]
    _ ↔ LocallyOfFinitePresentation q :=
      MorphismProperty.cancel_left_of_respectsIso
        @LocallyOfFinitePresentation c q
    _ ↔ r.globalSectionsKernelIdeal.FG :=
      quotient_lfp_iff_fg r.globalSectionsKernelIdeal

private lemma lfp_iff_forall_affine {X Z : Scheme.{u}} (i : Z ⟶ X) :
    LocallyOfFinitePresentation i ↔
      ∀ U : X.affineOpens, LocallyOfFinitePresentation (i ∣_ U) :=
  IsZariskiLocalAtTarget.iff_of_iSup_eq_top
    (P := @LocallyOfFinitePresentation) (fun U : X.affineOpens ↦ U.1)
      (iSup_affineOpens_eq_top X)

/-- A closed immersion is locally of finite presentation exactly when its kernel ideal sheaf is
of finite type. -/
@[stacks 01TV]
theorem closedImmersion_locallyOfFinitePresentation_iff_idealSheaf_isFiniteType
    {X Z : Scheme.{u}} {i : Z ⟶ X} (hi : IsClosedImmersion i) :
    LocallyOfFinitePresentation i ↔
      SheafOfModules.IsFiniteType (RingedSpace.Hom.idealSheaf i.toShHom) := by
  letI : IsClosedImmersion i := hi
  calc
    LocallyOfFinitePresentation i ↔
        ∀ U : X.affineOpens, LocallyOfFinitePresentation (i ∣_ U) :=
      lfp_iff_forall_affine i
    _ ↔ ∀ U : X.affineOpens,
        (LocallyRingedSpace.Hom.affineOpenKernelIdeal i.toLRSHom U).FG :=
      forall_congr' fun U ↦ local_lfp_iff_fg i U
    _ ↔ SheafOfModules.IsFiniteType
        (RingedSpace.Hom.idealSheaf i.toShHom) :=
      (ideal_isFiniteType_iff_forall_fg i).symm

/-- A closed immersion is of finite presentation exactly when its kernel ideal sheaf is of
finite type. -/
theorem closedImmersion_finitePresentation_iff_idealSheaf_isFiniteType
    {X Z : Scheme.{u}} {i : Z ⟶ X} (hi : IsClosedImmersion i) :
    Scheme.Hom.FinitePresentation i ↔
      SheafOfModules.IsFiniteType (RingedSpace.Hom.idealSheaf i.toShHom) := sorry

end AlgebraicGeometry
