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
        (ofOverMap (Over.homMk (morphismRestrict T.hom U) sorry) :
          ofOver VB.left ⟶ ofOver (openSmallEtale (Over.mk (𝟙 Y)) U).left)
        (iB.obj VB).hom sorry)
      sorry ≫
    (smallEtaleInclusion_comp_spacesEtalePullback g).hom.app VA

/-- `openPullbackHom T U` is an isomorphism of spaces-étale objects. -/
private instance isIso_openPullbackHom (T : Over Y) (U : Y.Opens) :
    IsIso (openPullbackHom T U) :=
  sorry

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

/-- `toSchemePushforwardHomOver` is an isomorphism on underlying modules. -/
instance isIso_toSchemePushforwardHomOver (T : Over Y) (N : (ofOver T).Modules) :
    IsIso (toSchemePushforwardHomOver T N) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
