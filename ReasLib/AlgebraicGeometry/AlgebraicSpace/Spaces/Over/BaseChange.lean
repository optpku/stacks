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

set_option backward.isDefEq.respectTransparency false

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
    (x : T.toGroupoids.total) : yonedaEquiv (pointHom x) = x.unop.2 := by
  exact yonedaEquiv.apply_symm_apply x.unop.2

/-- A morphism of points of `S_T` is compatible with the classified morphisms
`ofOver U ⟶ T`. -/
theorem pointHom_naturality {S : Scheme.{u}} {T : AlgebraicSpace S}
    {x y : T.toGroupoids.total} (φ : x ⟶ y) :
    pointHom x =
      (ofOverFunctor S).map (T.toGroupoids.p.map φ) ≫ pointHom y := by
  change yonedaEquiv.symm x.unop.2 =
    yoneda.map φ.unop.1.unop ≫ yonedaEquiv.symm y.unop.2
  rw [← yonedaEquiv_symm_map]
  exact congrArg yonedaEquiv.symm φ.unop.2.symm

/-- The morphism `X_U ⟶ X_V` induced by a morphism of scheme-points of `T`. -/
def pointBaseChangeLeft {S : Scheme.{u}} {T X : AlgebraicSpace S} (f : X ⟶ T)
    {x y : T.toGroupoids.total} (φ : x ⟶ y) :
    pullback f (pointHom x) ⟶ pullback f (pointHom y) :=
  pullback.lift (pullback.fst f (pointHom x))
    (pullback.snd f (pointHom x) ≫ (ofOverFunctor S).map (T.toGroupoids.p.map φ))
    (by
      exact (pullback.condition (f := f) (g := pointHom x)).trans
        ((congrArg (fun k : ofOver (T.toGroupoids.p.obj x) ⟶ T ↦
            pullback.snd f (pointHom x) ≫ k) (pointHom_naturality φ)).trans
          (Category.assoc _ _ _).symm))

/-- The comparison `X_U ⟶ X_V` commutes with the projections to `U` and `V`. -/
theorem pointBaseChangeLeft_snd {S : Scheme.{u}} {T X : AlgebraicSpace S}
    (f : X ⟶ T) {x y : T.toGroupoids.total} (φ : x ⟶ y) :
    pointBaseChangeLeft f φ ≫ pullback.snd f (pointHom y) =
      pullback.snd f (pointHom x) ≫
        (ofOverFunctor S).map (T.toGroupoids.p.map φ) := by
  exact pullback.lift_snd _ _ _

namespace FtOver

/-- A pullback square remains strongly cartesian when the objects of `Spaces`
are restricted to any full subcategory. -/
private theorem cartesian_of_pullback {S : Scheme.{u}}
    {P : ObjectProperty (Spaces S)} {A B : P.FullSubcategory} (φ : A ⟶ B)
    (h : IsPullback φ.hom.left A.obj.hom B.obj.hom ((ofOverFunctor S).map φ.hom.right)) :
    Functor.IsStronglyCartesian.property (P.ι ⋙ Spaces.p) φ := by
  refine { universal_property' := ?_ }
  intro R g ψ hψ
  have hbase := IsHomLift.eq_of_isHomLift (P.ι ⋙ Spaces.p)
    (g ≫ (P.ι ⋙ Spaces.p).map φ) ψ
  change g ≫ φ.hom.right = ψ.hom.right at hbase
  have hw : ψ.hom.left ≫ B.obj.hom =
      (R.obj.hom ≫ (ofOverFunctor S).map g) ≫ (ofOverFunctor S).map φ.hom.right := by
    rw [Category.assoc, ← CategoryTheory.Functor.map_comp, hbase]
    exact ψ.hom.w
  let χ : R ⟶ A :=
    { hom :=
        { left := h.lift ψ.hom.left (R.obj.hom ≫ (ofOverFunctor S).map g) hw
          right := g
          w := h.lift_snd _ _ _ } }
  refine ⟨χ, ⟨?_, ?_⟩, ?_⟩
  · exact IsHomLift.map (P.ι ⋙ Spaces.p) χ
  · apply ObjectProperty.hom_ext
    apply CommaMorphism.ext
    · exact h.lift_fst _ _ _
    · exact hbase
  · rintro τ ⟨hτlift, hτcomp⟩
    have ht : τ.hom.right = g :=
      (IsHomLift.eq_of_isHomLift (P.ι ⋙ Spaces.p) g τ).symm
    apply ObjectProperty.hom_ext
    apply CommaMorphism.ext
    · apply h.hom_ext
      · change τ.hom.left ≫ φ.hom.left =
          h.lift ψ.hom.left (R.obj.hom ≫ (ofOverFunctor S).map g) hw ≫ φ.hom.left
        rw [h.lift_fst]
        exact congrArg (fun ζ : R ⟶ B ↦ ζ.hom.left) hτcomp
      · change τ.hom.left ≫ A.obj.hom =
          h.lift ψ.hom.left (R.obj.hom ≫ (ofOverFunctor S).map g) hw ≫ A.obj.hom
        rw [h.lift_snd]
        simpa only [ht, CategoryTheory.Functor.id_map] using τ.hom.w
    · exact ht

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
      (pointSquare f φ) := by
  apply cartesian_of_pullback
  change IsPullback (pointBaseChangeLeft f φ) (pullback.snd f (pointHom x))
    (pullback.snd f (pointHom y)) ((ofOverFunctor S).map (T.toGroupoids.p.map φ))
  refine IsPullback.of_right ?_ (pointBaseChangeLeft_snd f φ)
    (IsPullback.of_hasPullback f (pointHom y))
  simpa only [pointBaseChangeLeft, pullback.lift_fst, ← pointHom_naturality φ] using
    (IsPullback.of_hasPullback f (pointHom x))

/-- The morphism of finite-type primed spaces `X_U ⟶ X_V` over `U ⟶ V`. -/
def pointMap {S : Scheme.{u}} {T X : AlgebraicSpace S} (f : X ⟶ T)
    [FiniteType f] {x y : T.toGroupoids.total} (φ : x ⟶ y) :
    pointObj f x ⟶ pointObj f y :=
  { hom := pointSquare f φ, property := pointSquare_isStronglyCartesian f φ }

/-- Identity morphisms of scheme-points act as identities on `X_U`. -/
theorem pointMap_id {S : Scheme.{u}} {T X : AlgebraicSpace S} (f : X ⟶ T)
    [FiniteType f] (x : T.toGroupoids.total) : pointMap f (𝟙 x) = 𝟙 (pointObj f x) := by
  apply WideSubcategory.hom_ext
  apply ObjectProperty.hom_ext
  apply CommaMorphism.ext
  · change pointBaseChangeLeft f (𝟙 x) = 𝟙 _
    apply pullback.hom_ext <;>
      simp only [pointBaseChangeLeft, CategoryTheory.Functor.map_id,
        Category.id_comp, Category.comp_id, pullback.lift_fst, pullback.lift_snd,
        ofOverFunctor]
  · exact T.toGroupoids.p.map_id x

/-- Base change of `X` along scheme-points of `T` preserves composition. -/
theorem pointMap_comp {S : Scheme.{u}} {T X : AlgebraicSpace S} (f : X ⟶ T)
    [FiniteType f] {x y z : T.toGroupoids.total} (φ : x ⟶ y) (ψ : y ⟶ z) :
    pointMap f (φ ≫ ψ) = pointMap f φ ≫ pointMap f ψ := by
  apply WideSubcategory.hom_ext
  apply ObjectProperty.hom_ext
  apply CommaMorphism.ext
  · change pointBaseChangeLeft f (φ ≫ ψ) = pointBaseChangeLeft f φ ≫ pointBaseChangeLeft f ψ
    apply pullback.hom_ext <;>
      simp only [pointBaseChangeLeft, CategoryTheory.Functor.map_comp, Category.assoc,
        pullback.lift_fst, pullback.lift_snd, pullback.lift_snd_assoc]
  · exact T.toGroupoids.p.map_comp φ ψ

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
  w := rfl

/-- The underlying functor of `baseChange f` is `baseChangeFunctor f`. -/
theorem baseChange_toFunctor {S : Scheme.{u}} {T X : AlgebraicSpace S}
    (f : X ⟶ T) [FiniteType f] :
    (baseChange f).toFunctor = baseChangeFunctor f := rfl

/-- `baseChange f` sends a point `x` to `FtGroupoids.mk` of the base-change
projection `X_U ⟶ U`. -/
theorem baseChange_obj {S : Scheme.{u}} {T X : AlgebraicSpace S} (f : X ⟶ T)
    [FiniteType f] (x : T.toGroupoids.total) :
    (baseChange f).obj x = FtGroupoids.mk (pullback.snd f (pointHom x)) := rfl

/-- The based functor `baseChange f` lies over `Over S`. -/
theorem baseChange_w {S : Scheme.{u}} {T X : AlgebraicSpace S} (f : X ⟶ T)
    [FiniteType f] :
    (baseChange f).toFunctor ⋙ pFtGroupoids S = T.toGroupoids.p := rfl

/-- The fibrewise morphism `X_U ⟶ Y_U` induced by a morphism of finite-type
spaces over `T`. -/
def yonedaAppLeft {S : Scheme.{u}} {T : AlgebraicSpace S} {P Q : FtOver T}
    (α : P ⟶ Q) (x : T.toGroupoids.total) :
    pullback P.of.obj.hom (pointHom x) ⟶ pullback Q.of.obj.hom (pointHom x) :=
  pullback.lift
    (pullback.fst P.of.obj.hom (pointHom x) ≫ homLeft α)
    (pullback.snd P.of.obj.hom (pointHom x)) (by
      rw [Category.assoc]
      change pullback.fst _ _ ≫ α.iso.hom.hom.left ≫ Q.of.obj.hom = _
      rw [Over.w α.iso.hom.hom]
      exact pullback.condition)

/-- `yonedaAppLeft` commutes with the projections to `U`. -/
theorem yonedaAppLeft_snd {S : Scheme.{u}} {T : AlgebraicSpace S}
    {P Q : FtOver T} (α : P ⟶ Q) (x : T.toGroupoids.total) :
    yonedaAppLeft α x ≫ pullback.snd Q.of.obj.hom (pointHom x) =
      pullback.snd P.of.obj.hom (pointHom x) ≫
        (ofOverFunctor S).map (𝟙 (T.toGroupoids.p.obj x)) := by
  rw [CategoryTheory.Functor.map_id]
  change yonedaAppLeft α x ≫ pullback.snd Q.of.obj.hom (pointHom x) =
    pullback.snd P.of.obj.hom (pointHom x) ≫ 𝟙 (ofOver (T.toGroupoids.p.obj x))
  rw [Category.comp_id]
  exact pullback.lift_snd (C := AlgebraicSpace S) _ _ _

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
      (yonedaSquare α x) := by
  haveI : IsIso (homLeft α) := by
    unfold homLeft
    infer_instance
  have hm : yonedaAppLeft α x =
      pullback.map P.of.obj.hom (pointHom x) Q.of.obj.hom (pointHom x)
        (homLeft α) (𝟙 _) (𝟙 _)
        (by exact (Category.comp_id _).trans (Over.w α.iso.hom.hom).symm)
        (by simp only [Category.id_comp, Category.comp_id]) := by
    apply pullback.hom_ext <;>
      simp only [yonedaAppLeft, pullback.map, pullback.lift_fst, pullback.lift_snd,
        Category.comp_id]
  haveI : IsIso (yonedaAppLeft α x) := by
    rw [hm]
    infer_instance
  apply cartesian_of_pullback
  change IsPullback (yonedaAppLeft α x) (pullback.snd P.of.obj.hom (pointHom x))
    (pullback.snd Q.of.obj.hom (pointHom x))
    ((ofOverFunctor S).map (𝟙 (T.toGroupoids.p.obj x)))
  apply IsPullback.of_horiz_isIso
  exact ⟨yonedaAppLeft_snd α x⟩

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
      yonedaApp α x ≫ (baseChange Q.of.obj.hom).map φ := by
  apply WideSubcategory.hom_ext
  apply ObjectProperty.hom_ext
  apply CommaMorphism.ext
  · change pointBaseChangeLeft P.of.obj.hom φ ≫ yonedaAppLeft α y =
        yonedaAppLeft α x ≫ pointBaseChangeLeft Q.of.obj.hom φ
    apply pullback.hom_ext <;>
      simp only [pointBaseChangeLeft, yonedaAppLeft, Category.assoc,
        pullback.lift_fst, pullback.lift_snd,
        pullback.lift_fst_assoc, pullback.lift_snd_assoc]
  · change T.toGroupoids.p.map φ ≫ 𝟙 _ = 𝟙 _ ≫ T.toGroupoids.p.map φ
    simp only [Category.comp_id, Category.id_comp]

/-- Fibrewise comparison morphisms lift identities of the base. -/
instance yonedaApp_isHomLift {S : Scheme.{u}} {T : AlgebraicSpace S}
    {P Q : FtOver T} (α : P ⟶ Q) (x : T.toGroupoids.total) :
    (FtGroupoids.toGroupoids S).p.IsHomLift (𝟙 (T.toGroupoids.p.obj x))
      (yonedaApp α x) := by
  exact IsHomLift.map (pFtGroupoids S) (yonedaApp α x)

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
    yonedaMap (𝟙 P) = 𝟙 (baseChange P.of.obj.hom) := by
  apply BasedNatTrans.ext
  apply NatTrans.ext
  funext x
  apply WideSubcategory.hom_ext
  apply ObjectProperty.hom_ext
  apply CommaMorphism.ext
  · change yonedaAppLeft (𝟙 P) x = 𝟙 _
    have hid : homLeft (𝟙 P) = 𝟙 P.of.obj.left := rfl
    apply pullback.hom_ext <;>
      simp only [yonedaAppLeft, hid, Category.comp_id, Category.id_comp,
        pullback.lift_fst, pullback.lift_snd]
  · rfl

/-- `yonedaMap` preserves composition in `FtOver T`. -/
theorem yonedaMap_comp {S : Scheme.{u}} {T : AlgebraicSpace S}
    {P Q R : FtOver T} (α : P ⟶ Q) (β : Q ⟶ R) :
    yonedaMap (α ≫ β) = yonedaMap α ≫ yonedaMap β := by
  apply BasedNatTrans.ext
  apply NatTrans.ext
  funext x
  apply WideSubcategory.hom_ext
  apply ObjectProperty.hom_ext
  apply CommaMorphism.ext
  · change yonedaAppLeft (α ≫ β) x = yonedaAppLeft α x ≫ yonedaAppLeft β x
    have hcomp : homLeft (α ≫ β) = homLeft α ≫ homLeft β := rfl
    apply pullback.hom_ext <;>
      simp only [yonedaAppLeft, hcomp, Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_fst_assoc]
  · change 𝟙 (T.toGroupoids.p.obj x) = 𝟙 _ ≫ 𝟙 _
    simp only [Category.id_comp]

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
    [FiniteType f] : (yoneda T).obj (mk f) = baseChange f := rfl

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
    pointMap f (𝟙 x) = 𝟙 (pointObj f x) := by
  apply ObjectProperty.hom_ext
  exact FtOver.pointMap_id f x

/-- Base change of `X` along scheme-points of `T` preserves composition. -/
theorem pointMap_comp {S : Scheme.{u}} {T X : AlgebraicSpace S} (f : X ⟶ T)
    [FpFlatProper f] {x y z : T.toGroupoids.total} (φ : x ⟶ y) (ψ : y ⟶ z) :
    pointMap f (φ ≫ ψ) = pointMap f φ ≫ pointMap f ψ := by
  apply ObjectProperty.hom_ext
  exact FtOver.pointMap_comp f φ ψ

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
  w := rfl

/-- The underlying functor of `baseChange f` is `baseChangeFunctor f`. -/
theorem baseChange_toFunctor {S : Scheme.{u}} {T X : AlgebraicSpace S}
    (f : X ⟶ T) [FpFlatProper f] :
    (baseChange f).toFunctor = baseChangeFunctor f := rfl

/-- `baseChange f` sends a point `x` to `FpFlatProperGroupoids.mk` of the
base-change projection `X_U ⟶ U`. -/
theorem baseChange_obj {S : Scheme.{u}} {T X : AlgebraicSpace S} (f : X ⟶ T)
    [FpFlatProper f] (x : T.toGroupoids.total) :
    (baseChange f).obj x =
      FpFlatProperGroupoids.mk (pullback.snd f (pointHom x)) := rfl

/-- The based functor `baseChange f` lies over `Over S`. -/
theorem baseChange_w {S : Scheme.{u}} {T X : AlgebraicSpace S} (f : X ⟶ T)
    [FpFlatProper f] :
    (baseChange f).toFunctor ⋙ pFpFlatProperGroupoids S = T.toGroupoids.p := rfl

/-- The fibrewise morphism `X_U ⟶ Y_U` induced by a morphism of fp-flat-proper
spaces over `T`. -/
def yonedaAppLeft {S : Scheme.{u}} {T : AlgebraicSpace S}
    {P Q : FpFlatProperOver T} (α : P ⟶ Q) (x : T.toGroupoids.total) :
    pullback P.of.obj.hom (pointHom x) ⟶ pullback Q.of.obj.hom (pointHom x) :=
  pullback.lift
    (pullback.fst P.of.obj.hom (pointHom x) ≫ homLeft α)
    (pullback.snd P.of.obj.hom (pointHom x)) (by
      rw [Category.assoc]
      change pullback.fst _ _ ≫ α.iso.hom.hom.left ≫ Q.of.obj.hom = _
      rw [Over.w α.iso.hom.hom]
      exact pullback.condition)

/-- `yonedaAppLeft` commutes with the projections to `U`. -/
theorem yonedaAppLeft_snd {S : Scheme.{u}} {T : AlgebraicSpace S}
    {P Q : FpFlatProperOver T} (α : P ⟶ Q) (x : T.toGroupoids.total) :
    yonedaAppLeft α x ≫ pullback.snd Q.of.obj.hom (pointHom x) =
      pullback.snd P.of.obj.hom (pointHom x) ≫
        (ofOverFunctor S).map (𝟙 (T.toGroupoids.p.obj x)) := by
  rw [CategoryTheory.Functor.map_id]
  change yonedaAppLeft α x ≫ pullback.snd Q.of.obj.hom (pointHom x) =
    pullback.snd P.of.obj.hom (pointHom x) ≫ 𝟙 (ofOver (T.toGroupoids.p.obj x))
  rw [Category.comp_id]
  exact pullback.lift_snd (C := AlgebraicSpace S) _ _ _

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
      (yonedaSquare α x) := by
  haveI : IsIso (homLeft α) := by
    unfold homLeft
    infer_instance
  have hm : yonedaAppLeft α x =
      pullback.map P.of.obj.hom (pointHom x) Q.of.obj.hom (pointHom x)
        (homLeft α) (𝟙 _) (𝟙 _)
        (by exact (Category.comp_id _).trans (Over.w α.iso.hom.hom).symm)
        (by simp only [Category.id_comp, Category.comp_id]) := by
    apply pullback.hom_ext <;>
      simp only [yonedaAppLeft, pullback.map, pullback.lift_fst, pullback.lift_snd,
        Category.comp_id]
  haveI : IsIso (yonedaAppLeft α x) := by
    rw [hm]
    infer_instance
  apply FtOver.cartesian_of_pullback
  change IsPullback (yonedaAppLeft α x) (pullback.snd P.of.obj.hom (pointHom x))
    (pullback.snd Q.of.obj.hom (pointHom x))
    ((ofOverFunctor S).map (𝟙 (T.toGroupoids.p.obj x)))
  apply IsPullback.of_horiz_isIso
  exact ⟨yonedaAppLeft_snd α x⟩

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
      yonedaApp α x ≫ (baseChange Q.of.obj.hom).map φ := by
  apply ObjectProperty.hom_ext
  apply WideSubcategory.hom_ext
  apply ObjectProperty.hom_ext
  apply CommaMorphism.ext
  · change pointBaseChangeLeft P.of.obj.hom φ ≫ yonedaAppLeft α y =
        yonedaAppLeft α x ≫ pointBaseChangeLeft Q.of.obj.hom φ
    apply pullback.hom_ext <;>
      simp only [pointBaseChangeLeft, yonedaAppLeft, Category.assoc,
        pullback.lift_fst, pullback.lift_snd,
        pullback.lift_fst_assoc, pullback.lift_snd_assoc]
  · change T.toGroupoids.p.map φ ≫ 𝟙 _ = 𝟙 _ ≫ T.toGroupoids.p.map φ
    simp only [Category.comp_id, Category.id_comp]

/-- Fibrewise comparison morphisms lift identities of the base. -/
instance yonedaApp_isHomLift {S : Scheme.{u}} {T : AlgebraicSpace S}
    {P Q : FpFlatProperOver T} (α : P ⟶ Q) (x : T.toGroupoids.total) :
    (FpFlatProperGroupoids.toGroupoids S).p.IsHomLift
      (𝟙 (T.toGroupoids.p.obj x)) (yonedaApp α x) := by
  exact IsHomLift.map (pFpFlatProperGroupoids S) (yonedaApp α x)

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
    yonedaMap (𝟙 P) = 𝟙 (baseChange P.of.obj.hom) := by
  apply BasedNatTrans.ext
  apply NatTrans.ext
  funext x
  apply ObjectProperty.hom_ext
  apply WideSubcategory.hom_ext
  apply ObjectProperty.hom_ext
  apply CommaMorphism.ext
  · change yonedaAppLeft (𝟙 P) x = 𝟙 _
    have hid : homLeft (𝟙 P) = 𝟙 P.of.obj.left := rfl
    apply pullback.hom_ext <;>
      simp only [yonedaAppLeft, hid, Category.comp_id, Category.id_comp,
        pullback.lift_fst, pullback.lift_snd]
  · rfl

/-- `yonedaMap` preserves composition in `FpFlatProperOver T`. -/
theorem yonedaMap_comp {S : Scheme.{u}} {T : AlgebraicSpace S}
    {P Q R : FpFlatProperOver T} (α : P ⟶ Q) (β : Q ⟶ R) :
    yonedaMap (α ≫ β) = yonedaMap α ≫ yonedaMap β := by
  apply BasedNatTrans.ext
  apply NatTrans.ext
  funext x
  apply ObjectProperty.hom_ext
  apply WideSubcategory.hom_ext
  apply ObjectProperty.hom_ext
  apply CommaMorphism.ext
  · change yonedaAppLeft (α ≫ β) x = yonedaAppLeft α x ≫ yonedaAppLeft β x
    have hcomp : homLeft (α ≫ β) = homLeft α ≫ homLeft β := rfl
    apply pullback.hom_ext <;>
      simp only [yonedaAppLeft, hcomp, Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_fst_assoc]
  · change 𝟙 (T.toGroupoids.p.obj x) = 𝟙 _ ≫ 𝟙 _
    simp only [Category.id_comp]

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
    [FpFlatProper f] : (yoneda T).obj (mk f) = baseChange f := rfl

end FpFlatProperOver

end AlgebraicGeometry.AlgebraicSpace.Spaces
