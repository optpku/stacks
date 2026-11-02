/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Restrict
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.SpacesHom
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.ToSpec
public import ReasLib.CategoryTheory.Sites.Topos.InternalModule

/-! # Comparison of étale module pushforward with scheme pushforward -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {Y : Scheme.{u}} {X : AlgebraicSpace Y}

/-- The structure morphism of a scheme over `Y`, as a morphism of algebraic spaces. -/
def overHomToBase (T : Over Y) : ofOver T ⟶ ofOver (Over.mk (𝟙 Y)) :=
  ofOverMap (Over.homMk T.hom (Category.comp_id T.hom))

/-- `overHomToBase T` is `ofOverMap` of `T.hom`. -/
theorem overHomToBase_eq (T : Over Y) :
    overHomToBase T = ofOverMap (Over.homMk T.hom (Category.comp_id T.hom)) :=
  rfl

/-- The small étale object of `ofOver U` associated to a Zariski open of `U.left`. -/
private def openSmallEtale (U : Over Y) (V : U.left.Opens) :
    smallEtaleSite (ofOver U) :=
  (schemeEtaleToSmallEtale U).obj
    ((smallEtaleToOpensRingedHom U.left).base.obj V)

/-- `openSmallEtale U V` is `schemeEtaleToSmallEtale` of the étale object of `V`. -/
private theorem openSmallEtale_eq (U : Over Y) (V : U.left.Opens) :
    openSmallEtale U V =
      (schemeEtaleToSmallEtale U).obj
        ((smallEtaleToOpensRingedHom U.left).base.obj V) :=
  rfl

/-- The spaces-étale comparison identifying the inverse-image open of `T.hom` with the
fibre product of a Zariski open of `Y`. -/
private def openPullbackHom (T : Over Y) (U : Y.Opens) :
    (smallEtaleToSpaces (ofOver T)).obj
        (openSmallEtale T (T.hom ⁻¹ᵁ U)) ⟶
      (etaleBaseChange (overHomToBase T)).obj
        (openSmallEtale (Over.mk (𝟙 Y)) U) :=
  let g := overHomToBase T
  let VB := openSmallEtale T (T.hom ⁻¹ᵁ U)
  let VA := openSmallEtale (Over.mk (𝟙 Y)) U
  let iB := smallEtaleToSpaces (ofOver T)
  MorphismProperty.Over.homMk
      (A := iB.obj VB)
      (B := (smallEtaleToSpaces (ofOver (Over.mk (𝟙 Y))) ⋙
          spacesEtalePullback g).obj VA)
      (pullback.lift
        (ofOverMap (Over.homMk (morphismRestrict T.hom U) (by
          change morphismRestrict T.hom U ≫ (U.ι ≫ 𝟙 Y) =
            (T.hom ⁻¹ᵁ U).ι ≫ T.hom
          simpa only [Category.comp_id] using morphismRestrict_ι T.hom U)) :
          ofOver VB.left ⟶ ofOver (openSmallEtale (Over.mk (𝟙 Y)) U).left)
        (iB.obj VB).hom (by
          change yoneda.map _ ≫ yoneda.map _ = yoneda.map _ ≫ yoneda.map _
          rw [← yoneda.map_comp, ← yoneda.map_comp]
          congr 1
          apply Over.OverMorphism.ext
          exact morphismRestrict_ι T.hom U))
      (by exact pullback.lift_snd _ _ _) ≫
    (smallEtaleInclusion_comp_spacesEtalePullback g).hom.app VA

/-- `openPullbackHom T U` is an isomorphism of spaces-étale objects. -/
private instance isIso_openPullbackHom (T : Over Y) (U : Y.Opens) :
    IsIso (openPullbackHom T U) := by
  let VA := openSmallEtale (Over.mk (𝟙 Y)) U
  let VB := openSmallEtale T (T.hom ⁻¹ᵁ U)
  let a : VB.left ⟶ VA.left := Over.homMk (morphismRestrict T.hom U) (by
    change morphismRestrict T.hom U ≫ (U.ι ≫ 𝟙 Y) = (T.hom ⁻¹ᵁ U).ι ≫ T.hom
    simpa only [Category.comp_id] using morphismRestrict_ι T.hom U)
  let b := schemeEtaleOverHom T
    ((smallEtaleToOpensRingedHom T.left).base.obj (T.hom ⁻¹ᵁ U))
  let c := schemeEtaleOverHom (Over.mk (𝟙 Y))
    ((smallEtaleToOpensRingedHom Y).base.obj U)
  let d : T ⟶ Over.mk (𝟙 Y) := Over.homMk T.hom (Category.comp_id T.hom)
  have h : IsPullback a b c d := by
    apply IsPullback.of_map (Over.forget Y)
    · apply Over.OverMorphism.ext
      exact morphismRestrict_ι T.hom U
    · exact isPullback_morphismRestrict T.hom U
  have hp := h.map yoneda
  have hp' : IsPullback (ofOverMap a) VB.hom VA.hom (overHomToBase T) := by
    refine IsPullback.of_isLimit (C := AlgebraicSpace Y)
      (PullbackCone.IsLimit.mk (C := AlgebraicSpace Y)
      (fst := ofOverMap a) (snd := VB.hom) (f := VA.hom) (g := overHomToBase T)
      (by exact hp.w)
      (fun s ↦ hp.lift (s.fst : s.pt.functorOfPoints ⟶ _) s.snd s.condition)
      (fun s ↦ hp.lift_fst _ _ _)
      (fun s ↦ hp.lift_snd _ _ _)
      (fun s m hm₁ hm₂ ↦ hp.hom_ext (k := (m : s.pt.functorOfPoints ⟶ _))
        (l := hp.lift (s.fst : s.pt.functorOfPoints ⟶ _) s.snd s.condition)
        (hm₁.trans (hp.lift_fst _ _ _).symm)
        (hm₂.trans (hp.lift_snd _ _ _).symm)))
  let e : ofOver VB.left ≅ Limits.pullback VA.hom (overHomToBase T) :=
    hp'.isoPullback
  let i : (smallEtaleToSpaces (ofOver T)).obj VB ≅
      (smallEtaleToSpaces (ofOver (Over.mk (𝟙 Y))) ⋙
        spacesEtalePullback (overHomToBase T)).obj VA :=
    MorphismProperty.Over.isoMk e (by exact hp'.isoPullback_hom_snd)
  have hi : openPullbackHom T U =
      i.hom ≫ (smallEtaleInclusion_comp_spacesEtalePullback (overHomToBase T)).hom.app VA := by
    dsimp only [openPullbackHom]
    congr 1
  rw [hi]
  infer_instance

/-- Type-valued component of the `toScheme` direct-image comparison at an open of `Y`. -/
private def toSchemePushforwardUnderlyingAppOver (T : Over Y) (N : (ofOver T).Modules)
    (U : Y.Opensᵒᵖ) :
    ((Sheaf.InternalModule.ToInternal.underlying Y.ringCatSheaf).obj
        ((toScheme (Over.mk (𝟙 Y))).obj
          ((pushforward (overHomToBase T)).obj
            N))).obj.obj U ⟶
      ((Sheaf.InternalModule.ToInternal.underlying Y.ringCatSheaf).obj
        ((Scheme.Modules.pushforward T.hom).obj ((toScheme T).obj N))).obj.obj U :=
  let g := overHomToBase T
  let VA := openSmallEtale (Over.mk (𝟙 Y)) (unop U)
  let VB := openSmallEtale T (T.hom ⁻¹ᵁ unop U)
  let Nty :=
    (Sheaf.InternalModule.ToInternal.underlying (structureSheaf (ofOver T))).obj N
  let a : (smallEtaleToSpaces (ofOver T)).obj VB ⟶ (etaleBaseChange g).obj VA :=
    openPullbackHom T (unop U)
  let evaluation :
      ((EtaleTopos.extension (ofOver T)).obj Nty).obj.obj
          (op ((etaleBaseChange g).obj VA)) ⟶ Nty.obj.obj (op VB) :=
    EtaleTopos.extensionEvaluation (ofOver T) Nty a
  ((RingedSite.ToposHom.ModulePushforward.forgetIso (ringedToposHom g)).hom.app N).hom.app
      (op VA) ≫
    evaluation

/-- Type-valued sheaf morphism of the `toScheme` direct-image comparison along `T.hom`. -/
private def toSchemePushforwardUnderlyingOver (T : Over Y) (N : (ofOver T).Modules) :
    (Sheaf.InternalModule.ToInternal.underlying Y.ringCatSheaf).obj
      ((toScheme (Over.mk (𝟙 Y))).obj
        ((pushforward (overHomToBase T)).obj N)) ⟶
      (Sheaf.InternalModule.ToInternal.underlying Y.ringCatSheaf).obj
        ((Scheme.Modules.pushforward T.hom).obj ((toScheme T).obj N)) :=
  { hom :=
      { app := fun U ↦ toSchemePushforwardUnderlyingAppOver T N U
        naturality := fun _ _ _ ↦ sorry } }

/-- Direct-image comparison of `toScheme` against Zariski pushforward along `T.hom`. -/
@[no_expose]
def toSchemePushforwardHomOver (T : Over Y) (N : (ofOver T).Modules) :
    (toScheme (Over.mk (𝟙 Y))).obj
        ((pushforward (overHomToBase T)).obj N) ⟶
      (Scheme.Modules.pushforward T.hom).obj ((toScheme T).obj N) :=
  Sheaf.InternalModule.homOfUnderlying Y.ringCatSheaf
    (toSchemePushforwardUnderlyingOver T N) sorry sorry

set_option maxHeartbeats 800000 in
/-- `toSchemePushforwardHomOver` is an isomorphism on underlying modules. -/
instance isIso_toSchemePushforwardHomOver (T : Over Y) (N : (ofOver T).Modules) :
    IsIso (toSchemePushforwardHomOver T N) := by
  let f := toSchemePushforwardHomOver T N
  haveI (U : Y.Opensᵒᵖ) : IsIso ((forget _).map (f.val.app U)) := by
    let VA := openSmallEtale (Over.mk (𝟙 Y)) (unop U)
    let VB := openSmallEtale T (T.hom ⁻¹ᵁ unop U)
    let Nty := (Sheaf.InternalModule.ToInternal.underlying (structureSheaf (ofOver T))).obj N
    let e₁ := ((sheafToPresheaf (smallEtaleTopology (ofOver (Over.mk (𝟙 Y))))
      (Type u)).mapIso
      ((RingedSite.ToposHom.ModulePushforward.forgetIso
        (ringedToposHom (overHomToBase T))).app N)).app (op VA)
    let e₂ := ((EtaleTopos.extension (ofOver T)).obj Nty).obj.mapIso
      (asIso (openPullbackHom T (unop U))).op
    let e₃ := ((sheafToPresheaf (smallEtaleTopology (ofOver T)) (Type u)).mapIso
      ((EtaleTopos.extensionRestrictionIso (ofOver T)).app Nty)).app (op VB)
    change IsIso (toSchemePushforwardUnderlyingAppOver T N U)
    dsimp only [toSchemePushforwardUnderlyingAppOver, EtaleTopos.extensionEvaluation]
    exact (e₁ ≪≫ e₂ ≪≫ e₃).isIso_hom
  haveI (U : Y.Opensᵒᵖ) : IsIso (f.val.app U) :=
    isIso_of_reflects_iso _ (forget _)
  let e := PresheafOfModules.isoMk (fun U ↦ asIso (f.val.app U))
    (by intro U V g; exact f.val.naturality g)
  exact @isIso_of_reflects_iso _ _ _ _ _ _ f
    (SheafOfModules.forget Y.ringCatSheaf) e.isIso_hom
    (SheafOfModules.fullyFaithfulForget Y.ringCatSheaf).reflectsIsomorphisms

end AlgebraicGeometry.AlgebraicSpace.Modules
