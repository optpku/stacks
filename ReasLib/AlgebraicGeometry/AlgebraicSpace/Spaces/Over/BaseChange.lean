/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoids
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Spaces.Groupoids
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Spaces.Over

/-!
# Base change from morphisms over an algebraic space into primed stacks

A finite-type morphism `X ⟶ T` determines a based functor `S_T ⥤ᵇ Spaces'_ft`
by sending a scheme-point of `T` to the base change `X_U ⟶ U`. Packing this
assignment on the groupoid of finite-type morphisms over `T` yields the
comparison functor to based functors. The fp-flat-proper variant is analogous.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Spaces CategoryTheory.Limits
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces

/-- The morphism `ofOver U ⟶ T` classified by a point of the groupoid fibration
`S_T` associated to an algebraic space `T`. -/
def pointHom {S : Scheme.{u}} {T : AlgebraicSpace S} (x : T.toGroupoids.total) :
    ofOver (T.toGroupoids.p.obj x) ⟶ T :=
  yonedaEquiv.symm x.unop.2

/-- `pointHom x` is the Yoneda transpose of the functor-of-points element carried
by `x`. -/
theorem pointHom_spec {S : Scheme.{u}} {T : AlgebraicSpace S}
    (x : T.toGroupoids.total) : yonedaEquiv (pointHom x) = x.unop.2 := sorry

/-- A morphism of points of `S_T` is compatible with the classified morphisms
`ofOver U ⟶ T`. -/
theorem pointHom_naturality {S : Scheme.{u}} {T : AlgebraicSpace S}
    {x y : T.toGroupoids.total} (φ : x ⟶ y) :
    pointHom x =
      (ofOverFunctor S).map (T.toGroupoids.p.map φ) ≫ pointHom y := sorry

/-- The morphism `X_U ⟶ X_V` induced by a morphism of scheme-points of `T`. -/
def pointBaseChangeLeft {S : Scheme.{u}} {T X : AlgebraicSpace S} (f : X ⟶ T)
    {x y : T.toGroupoids.total} (φ : x ⟶ y) :
    pullback f (pointHom x) ⟶ pullback f (pointHom y) :=
  pullback.lift (pullback.fst f (pointHom x))
    (pullback.snd f (pointHom x) ≫ (ofOverFunctor S).map (T.toGroupoids.p.map φ))
    (by sorry)

/-- The comparison `X_U ⟶ X_V` commutes with the projections to `U` and `V`. -/
theorem pointBaseChangeLeft_snd {S : Scheme.{u}} {T X : AlgebraicSpace S}
    (f : X ⟶ T) {x y : T.toGroupoids.total} (φ : x ⟶ y) :
    pointBaseChangeLeft f φ ≫ pullback.snd f (pointHom y) =
      pullback.snd f (pointHom x) ≫
        (ofOverFunctor S).map (T.toGroupoids.p.map φ) := sorry

namespace FtOver

/-- The finite-type primed space `X_U ⟶ U` obtained by base change of `f` along
a scheme-point of `T`. -/
abbrev pointObj {S : Scheme.{u}} {T X : AlgebraicSpace S} (f : X ⟶ T)
    [FiniteType f] (x : T.toGroupoids.total) : FtGroupoids S :=
  FtGroupoids.mk (pullback.snd f (pointHom x))

/-- The underlying square of the base-change morphism of finite-type primed
spaces along a morphism of scheme-points of `T`. -/
def pointSquare {S : Scheme.{u}} {T X : AlgebraicSpace S} (f : X ⟶ T)
    [FiniteType f] {x y : T.toGroupoids.total} (φ : x ⟶ y) :
    (pointObj f x).obj ⟶ (pointObj f y).obj :=
  { hom :=
      { left := pointBaseChangeLeft f φ
        right := T.toGroupoids.p.map φ
        w := pointBaseChangeLeft_snd f φ } }

/-- The underlying square of `pointSquare` is strongly cartesian. -/
theorem pointSquare_isStronglyCartesian {S : Scheme.{u}} {T X : AlgebraicSpace S}
    (f : X ⟶ T) [FiniteType f] {x y : T.toGroupoids.total} (φ : x ⟶ y) :
    Functor.IsStronglyCartesian.property ((finiteType S).ι ⋙ Spaces.p)
      (pointSquare f φ) := sorry

/-- The morphism of finite-type primed spaces `X_U ⟶ X_V` over `U ⟶ V`. -/
def pointMap {S : Scheme.{u}} {T X : AlgebraicSpace S} (f : X ⟶ T)
    [FiniteType f] {x y : T.toGroupoids.total} (φ : x ⟶ y) :
    pointObj f x ⟶ pointObj f y :=
  { hom := pointSquare f φ, property := pointSquare_isStronglyCartesian f φ }

/-- Identity morphisms of scheme-points act as identities on `X_U`. -/
theorem pointMap_id {S : Scheme.{u}} {T X : AlgebraicSpace S} (f : X ⟶ T)
    [FiniteType f] (x : T.toGroupoids.total) : pointMap f (𝟙 x) = 𝟙 (pointObj f x) :=
  sorry

/-- Base change of `X` along scheme-points of `T` preserves composition. -/
theorem pointMap_comp {S : Scheme.{u}} {T X : AlgebraicSpace S} (f : X ⟶ T)
    [FiniteType f] {x y z : T.toGroupoids.total} (φ : x ⟶ y) (ψ : y ⟶ z) :
    pointMap f (φ ≫ ψ) = pointMap f φ ≫ pointMap f ψ := sorry

/-- The total functor sending a scheme-point of `T` to the finite-type primed
space `X_U ⟶ U`. -/
def baseChangeFunctor {S : Scheme.{u}} {T X : AlgebraicSpace S} (f : X ⟶ T)
    [FiniteType f] : T.toGroupoids.total ⥤ FtGroupoids S where
  obj := pointObj f
  map := pointMap f
  map_id := pointMap_id f
  map_comp := pointMap_comp f

/-- Base change of a finite-type
morphism `X ⟶ T` along scheme-points of `T` is a based functor
`S_T ⥤ᵇ Spaces'_ft`. -/
def baseChange {S : Scheme.{u}} {T X : AlgebraicSpace S} (f : X ⟶ T)
    [FiniteType f] :
    T.toGroupoids.toBasedCategory ⥤ᵇ (FtGroupoids.toGroupoids S).toBasedCategory where
  toFunctor := baseChangeFunctor f
  w := sorry

/-- The underlying functor of `baseChange f` is `baseChangeFunctor f`. -/
theorem baseChange_toFunctor {S : Scheme.{u}} {T X : AlgebraicSpace S}
    (f : X ⟶ T) [FiniteType f] :
    (baseChange f).toFunctor = baseChangeFunctor f := sorry

/-- `baseChange f` sends a point `x` to `FtGroupoids.mk` of the base-change
projection `X_U ⟶ U`. -/
theorem baseChange_obj {S : Scheme.{u}} {T X : AlgebraicSpace S} (f : X ⟶ T)
    [FiniteType f] (x : T.toGroupoids.total) :
    (baseChange f).obj x = FtGroupoids.mk (pullback.snd f (pointHom x)) := sorry

/-- The based functor `baseChange f` lies over `Over S`. -/
theorem baseChange_w {S : Scheme.{u}} {T X : AlgebraicSpace S} (f : X ⟶ T)
    [FiniteType f] :
    (baseChange f).toFunctor ⋙ pFtGroupoids S = T.toGroupoids.p := sorry

/-- The fibrewise morphism `X_U ⟶ Y_U` induced by a morphism of finite-type
spaces over `T`. -/
def yonedaAppLeft {S : Scheme.{u}} {T : AlgebraicSpace S} {P Q : FtOver T}
    (α : P ⟶ Q) (x : T.toGroupoids.total) :
    pullback P.of.obj.hom (pointHom x) ⟶ pullback Q.of.obj.hom (pointHom x) :=
  pullback.lift
    (pullback.fst P.of.obj.hom (pointHom x) ≫ homLeft α)
    (pullback.snd P.of.obj.hom (pointHom x)) (by sorry)

/-- `yonedaAppLeft` commutes with the projections to `U`. -/
theorem yonedaAppLeft_snd {S : Scheme.{u}} {T : AlgebraicSpace S}
    {P Q : FtOver T} (α : P ⟶ Q) (x : T.toGroupoids.total) :
    yonedaAppLeft α x ≫ pullback.snd Q.of.obj.hom (pointHom x) =
      pullback.snd P.of.obj.hom (pointHom x) ≫
        (ofOverFunctor S).map (𝟙 (T.toGroupoids.p.obj x)) := sorry

/-- The underlying square of the fibrewise comparison of `baseChange` along a
morphism of `FtOver T`. -/
def yonedaSquare {S : Scheme.{u}} {T : AlgebraicSpace S} {P Q : FtOver T}
    (α : P ⟶ Q) (x : T.toGroupoids.total) :
    (pointObj P.of.obj.hom x).obj ⟶ (pointObj Q.of.obj.hom x).obj :=
  { hom :=
      { left := yonedaAppLeft α x
        right := 𝟙 (T.toGroupoids.p.obj x)
        w := yonedaAppLeft_snd α x } }

/-- The fibrewise comparison square is strongly cartesian. -/
theorem yonedaSquare_isStronglyCartesian {S : Scheme.{u}} {T : AlgebraicSpace S}
    {P Q : FtOver T} (α : P ⟶ Q) (x : T.toGroupoids.total) :
    Functor.IsStronglyCartesian.property ((finiteType S).ι ⋙ Spaces.p)
      (yonedaSquare α x) := sorry

/-- The component at a scheme-point of `T` of the based natural transformation
associated to a morphism of `FtOver T`. -/
def yonedaApp {S : Scheme.{u}} {T : AlgebraicSpace S} {P Q : FtOver T}
    (α : P ⟶ Q) (x : T.toGroupoids.total) :
    (baseChange P.of.obj.hom).obj x ⟶ (baseChange Q.of.obj.hom).obj x :=
  { hom := yonedaSquare α x, property := yonedaSquare_isStronglyCartesian α x }

/-- Components of `yonedaApp` are natural in scheme-points of `T`. -/
theorem yonedaApp_naturality {S : Scheme.{u}} {T : AlgebraicSpace S}
    {P Q : FtOver T} (α : P ⟶ Q)
    ⦃x y : T.toGroupoids.total⦄ (φ : x ⟶ y) :
    (baseChange P.of.obj.hom).map φ ≫ yonedaApp α y =
      yonedaApp α x ≫ (baseChange Q.of.obj.hom).map φ := sorry

/-- Fibrewise comparison morphisms lift identities of the base. -/
instance yonedaApp_isHomLift {S : Scheme.{u}} {T : AlgebraicSpace S}
    {P Q : FtOver T} (α : P ⟶ Q) (x : T.toGroupoids.total) :
    (FtGroupoids.toGroupoids S).p.IsHomLift (𝟙 (T.toGroupoids.p.obj x))
      (yonedaApp α x) := sorry

/-- The based natural transformation `baseChange X ⟶ baseChange Y` induced by a
morphism of finite-type spaces over `T`. -/
def yonedaMap {S : Scheme.{u}} {T : AlgebraicSpace S} {P Q : FtOver T}
    (α : P ⟶ Q) : baseChange P.of.obj.hom ⟶ baseChange Q.of.obj.hom where
  app := yonedaApp α
  naturality := yonedaApp_naturality α
  isHomLift' := yonedaApp_isHomLift α

/-- Identity morphisms of `FtOver T` act as identity based natural
transformations. -/
theorem yonedaMap_id {S : Scheme.{u}} {T : AlgebraicSpace S} (P : FtOver T) :
    yonedaMap (𝟙 P) = 𝟙 (baseChange P.of.obj.hom) := sorry

/-- `yonedaMap` preserves composition in `FtOver T`. -/
theorem yonedaMap_comp {S : Scheme.{u}} {T : AlgebraicSpace S}
    {P Q R : FtOver T} (α : P ⟶ Q) (β : Q ⟶ R) :
    yonedaMap (α ≫ β) = yonedaMap α ≫ yonedaMap β := sorry

/-- The comparison functor sending a
finite-type morphism `X ⟶ T` to the based functor `U/T ↦ X_U → U`. -/
def yoneda {S : Scheme.{u}} (T : AlgebraicSpace S) :
    FtOver T ⥤
      (T.toGroupoids.toBasedCategory ⥤ᵇ
        (FtGroupoids.toGroupoids S).toBasedCategory) where
  obj P := baseChange P.of.obj.hom
  map := yonedaMap
  map_id := yonedaMap_id
  map_comp := yonedaMap_comp

/-- `yoneda` sends `mk f` to `baseChange f`. -/
theorem yoneda_obj {S : Scheme.{u}} {T X : AlgebraicSpace S} (f : X ⟶ T)
    [FiniteType f] : (yoneda T).obj (mk f) = baseChange f := sorry

end FtOver

namespace FpFlatProperOver

/-- The fp-flat-proper primed space `X_U ⟶ U` obtained by base change of `f`
along a scheme-point of `T`. -/
abbrev pointObj {S : Scheme.{u}} {T X : AlgebraicSpace S} (f : X ⟶ T)
    [FpFlatProper f] (x : T.toGroupoids.total) : FpFlatProperGroupoids S :=
  FpFlatProperGroupoids.mk (pullback.snd f (pointHom x))

/-- The morphism of fp-flat-proper primed spaces `X_U ⟶ X_V` over `U ⟶ V`. -/
def pointMap {S : Scheme.{u}} {T X : AlgebraicSpace S} (f : X ⟶ T)
    [FpFlatProper f] {x y : T.toGroupoids.total} (φ : x ⟶ y) :
    pointObj f x ⟶ pointObj f y :=
  { hom := FtOver.pointMap f φ }

/-- Identity morphisms of scheme-points act as identities on `X_U`. -/
theorem pointMap_id {S : Scheme.{u}} {T X : AlgebraicSpace S} (f : X ⟶ T)
    [FpFlatProper f] (x : T.toGroupoids.total) :
    pointMap f (𝟙 x) = 𝟙 (pointObj f x) := sorry

/-- Base change of `X` along scheme-points of `T` preserves composition. -/
theorem pointMap_comp {S : Scheme.{u}} {T X : AlgebraicSpace S} (f : X ⟶ T)
    [FpFlatProper f] {x y z : T.toGroupoids.total} (φ : x ⟶ y) (ψ : y ⟶ z) :
    pointMap f (φ ≫ ψ) = pointMap f φ ≫ pointMap f ψ := sorry

/-- The total functor sending a scheme-point of `T` to the fp-flat-proper primed
space `X_U ⟶ U`. -/
def baseChangeFunctor {S : Scheme.{u}} {T X : AlgebraicSpace S} (f : X ⟶ T)
    [FpFlatProper f] : T.toGroupoids.total ⥤ FpFlatProperGroupoids S where
  obj := pointObj f
  map := pointMap f
  map_id := pointMap_id f
  map_comp := pointMap_comp f

/-- Base change of an
fp-flat-proper morphism `X ⟶ T` along scheme-points of `T` is a based functor
`S_T ⥤ᵇ Spaces'_{fp, flat, proper}`. -/
def baseChange {S : Scheme.{u}} {T X : AlgebraicSpace S} (f : X ⟶ T)
    [FpFlatProper f] :
    T.toGroupoids.toBasedCategory ⥤ᵇ
      (FpFlatProperGroupoids.toGroupoids S).toBasedCategory where
  toFunctor := baseChangeFunctor f
  w := sorry

/-- The underlying functor of `baseChange f` is `baseChangeFunctor f`. -/
theorem baseChange_toFunctor {S : Scheme.{u}} {T X : AlgebraicSpace S}
    (f : X ⟶ T) [FpFlatProper f] :
    (baseChange f).toFunctor = baseChangeFunctor f := sorry

/-- `baseChange f` sends a point `x` to `FpFlatProperGroupoids.mk` of the
base-change projection `X_U ⟶ U`. -/
theorem baseChange_obj {S : Scheme.{u}} {T X : AlgebraicSpace S} (f : X ⟶ T)
    [FpFlatProper f] (x : T.toGroupoids.total) :
    (baseChange f).obj x =
      FpFlatProperGroupoids.mk (pullback.snd f (pointHom x)) := sorry

/-- The based functor `baseChange f` lies over `Over S`. -/
theorem baseChange_w {S : Scheme.{u}} {T X : AlgebraicSpace S} (f : X ⟶ T)
    [FpFlatProper f] :
    (baseChange f).toFunctor ⋙ pFpFlatProperGroupoids S = T.toGroupoids.p :=
  sorry

/-- The fibrewise morphism `X_U ⟶ Y_U` induced by a morphism of fp-flat-proper
spaces over `T`. -/
def yonedaAppLeft {S : Scheme.{u}} {T : AlgebraicSpace S}
    {P Q : FpFlatProperOver T} (α : P ⟶ Q) (x : T.toGroupoids.total) :
    pullback P.of.obj.hom (pointHom x) ⟶ pullback Q.of.obj.hom (pointHom x) :=
  pullback.lift
    (pullback.fst P.of.obj.hom (pointHom x) ≫ homLeft α)
    (pullback.snd P.of.obj.hom (pointHom x)) (by sorry)

/-- `yonedaAppLeft` commutes with the projections to `U`. -/
theorem yonedaAppLeft_snd {S : Scheme.{u}} {T : AlgebraicSpace S}
    {P Q : FpFlatProperOver T} (α : P ⟶ Q) (x : T.toGroupoids.total) :
    yonedaAppLeft α x ≫ pullback.snd Q.of.obj.hom (pointHom x) =
      pullback.snd P.of.obj.hom (pointHom x) ≫
        (ofOverFunctor S).map (𝟙 (T.toGroupoids.p.obj x)) := sorry

/-- The underlying `FtGroupoids` square of the fibrewise comparison along a
morphism of `FpFlatProperOver T`. -/
def yonedaSquare {S : Scheme.{u}} {T : AlgebraicSpace S}
    {P Q : FpFlatProperOver T} (α : P ⟶ Q) (x : T.toGroupoids.total) :
    (FtOver.pointObj P.of.obj.hom x).obj ⟶ (FtOver.pointObj Q.of.obj.hom x).obj :=
  { hom :=
      { left := yonedaAppLeft α x
        right := 𝟙 (T.toGroupoids.p.obj x)
        w := yonedaAppLeft_snd α x } }

/-- The fibrewise comparison square is strongly cartesian. -/
theorem yonedaSquare_isStronglyCartesian {S : Scheme.{u}} {T : AlgebraicSpace S}
    {P Q : FpFlatProperOver T} (α : P ⟶ Q) (x : T.toGroupoids.total) :
    Functor.IsStronglyCartesian.property ((finiteType S).ι ⋙ Spaces.p)
      (yonedaSquare α x) := sorry

/-- The `FtGroupoids` component of the fibrewise comparison. -/
def yonedaAppFt {S : Scheme.{u}} {T : AlgebraicSpace S}
    {P Q : FpFlatProperOver T} (α : P ⟶ Q) (x : T.toGroupoids.total) :
    FtOver.pointObj P.of.obj.hom x ⟶ FtOver.pointObj Q.of.obj.hom x :=
  { hom := yonedaSquare α x, property := yonedaSquare_isStronglyCartesian α x }

/-- The component at a scheme-point of `T` of the based natural transformation
associated to a morphism of `FpFlatProperOver T`. -/
def yonedaApp {S : Scheme.{u}} {T : AlgebraicSpace S} {P Q : FpFlatProperOver T}
    (α : P ⟶ Q) (x : T.toGroupoids.total) :
    (baseChange P.of.obj.hom).obj x ⟶ (baseChange Q.of.obj.hom).obj x :=
  { hom := yonedaAppFt α x }

/-- Components of `yonedaApp` are natural in scheme-points of `T`. -/
theorem yonedaApp_naturality {S : Scheme.{u}} {T : AlgebraicSpace S}
    {P Q : FpFlatProperOver T} (α : P ⟶ Q)
    ⦃x y : T.toGroupoids.total⦄ (φ : x ⟶ y) :
    (baseChange P.of.obj.hom).map φ ≫ yonedaApp α y =
      yonedaApp α x ≫ (baseChange Q.of.obj.hom).map φ := sorry

/-- Fibrewise comparison morphisms lift identities of the base. -/
instance yonedaApp_isHomLift {S : Scheme.{u}} {T : AlgebraicSpace S}
    {P Q : FpFlatProperOver T} (α : P ⟶ Q) (x : T.toGroupoids.total) :
    (FpFlatProperGroupoids.toGroupoids S).p.IsHomLift
      (𝟙 (T.toGroupoids.p.obj x)) (yonedaApp α x) := sorry

/-- The based natural transformation `baseChange X ⟶ baseChange Y` induced by a
morphism of fp-flat-proper spaces over `T`. -/
def yonedaMap {S : Scheme.{u}} {T : AlgebraicSpace S} {P Q : FpFlatProperOver T}
    (α : P ⟶ Q) : baseChange P.of.obj.hom ⟶ baseChange Q.of.obj.hom where
  app := yonedaApp α
  naturality := yonedaApp_naturality α
  isHomLift' := yonedaApp_isHomLift α

/-- Identity morphisms of `FpFlatProperOver T` act as identity based natural
transformations. -/
theorem yonedaMap_id {S : Scheme.{u}} {T : AlgebraicSpace S}
    (P : FpFlatProperOver T) :
    yonedaMap (𝟙 P) = 𝟙 (baseChange P.of.obj.hom) := sorry

/-- `yonedaMap` preserves composition in `FpFlatProperOver T`. -/
theorem yonedaMap_comp {S : Scheme.{u}} {T : AlgebraicSpace S}
    {P Q R : FpFlatProperOver T} (α : P ⟶ Q) (β : Q ⟶ R) :
    yonedaMap (α ≫ β) = yonedaMap α ≫ yonedaMap β := sorry

/-- The comparison functor sending an
fp-flat-proper morphism `X ⟶ T` to the based functor `U/T ↦ X_U → U`. -/
def yoneda {S : Scheme.{u}} (T : AlgebraicSpace S) :
    FpFlatProperOver T ⥤
      (T.toGroupoids.toBasedCategory ⥤ᵇ
        (FpFlatProperGroupoids.toGroupoids S).toBasedCategory) where
  obj P := baseChange P.of.obj.hom
  map := yonedaMap
  map_id := yonedaMap_id
  map_comp := yonedaMap_comp

/-- `yoneda` sends `mk f` to `baseChange f`. -/
theorem yoneda_obj {S : Scheme.{u}} {T X : AlgebraicSpace S} (f : X ⟶ T)
    [FpFlatProper f] : (yoneda T).obj (mk f) = baseChange f := sorry

end FpFlatProperOver

end AlgebraicGeometry.AlgebraicSpace.Spaces
