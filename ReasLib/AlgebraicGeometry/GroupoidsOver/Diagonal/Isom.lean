/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Reindex.NatIso
public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Pseudofunctor
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.Fiber
public import ReasLib.CategoryTheory.Fibered.HomPresheaf.Isom
public import ReasLib.CategoryTheory.Sites.Descent.HomPresheaf.Isom
public import ReasLib.CategoryTheory.Sites.Descent.HomPresheaf.StrongTrans
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Basic

/-!
# Isomorphism-presheaf maps along morphisms of groupoid fibrations

A 1-morphism `f : X ⟶ Y` of categories fibred in groupoids induces
`Isom_X(x, x') ⟶ Isom_Y(f(x), f(x'))`. A fibrewise isomorphism
`α : f(x) ≅ f(x')` transposes to a section of the target over `T`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite Functor
open FiberedCategoryOver.Groupoids
open scoped Bicategory CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}

/-- Size-stable isomorphism presheaf `Isom_X(x, x')` on `Over T`. -/
abbrev isom {T : Over S} (x x' : X.p.Fiber T) :
    (Over T)ᵒᵖ ⥤ Type (u + 1) :=
  Functor.isomorphismPresheafULift X.p x x'

set_option backward.isDefEq.respectTransparency false in
/-- Strong transformation of fibre pseudofunctors induced by a morphism of
categories fibred in groupoids. -/
def homStrongTrans (f : X ⟶ Y) :
    Pseudofunctor.StrongTrans
      (Functor.fiberPseudofunctor X.p) (Functor.fiberPseudofunctor Y.p) where
  app U := (fiberFunctor f (unop U.as)).toCatHom
  naturality g :=
    Cat.Hom.isoMk
      (CartesianBasedFunctor.Reindex.natIso (toCartesianBasedFunctor f)
        (Functor.Cleavage.ofIsFibered X.p) (Functor.Cleavage.ofIsFibered Y.p)
        g.as.unop).symm
  naturality_naturality := by
    intro U V g h η
    obtain rfl := LocallyDiscrete.eq_of_hom η
    have hη : η = 𝟙 g := Subsingleton.elim _ _
    subst η
    simp
  naturality_id := by
    intro U
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext x
    change
      (CartesianBasedFunctor.Reindex.mapIso (toCartesianBasedFunctor f)
        (Functor.Cleavage.ofIsFibered X.p) (Functor.Cleavage.ofIsFibered Y.p)
        (𝟙 (unop U.as)) x).inv ≫
          (Functor.Chosen.Reindex.idIsoApp Y.p (unop U.as)
            ((fiberFunctor f (unop U.as)).obj x)).inv =
        (fiberFunctor f (unop U.as)).map
            (Functor.Chosen.Reindex.idIsoApp X.p (unop U.as) x).inv ≫ 𝟙 _ ≫ 𝟙 _
    simp only [Category.comp_id]
    apply Functor.Fiber.hom_ext
    change _ ≫ (Functor.Chosen.Reindex.idIsoApp Y.p _ _).inv.1 =
      ((fiberFunctor f _).map (Functor.Chosen.Reindex.idIsoApp X.p _ x).inv).1
    rw [Functor.Chosen.Reindex.idIsoApp.inv.eq_cartesianHom, fiberFunctor.map.val,
      Functor.Chosen.Reindex.idIsoApp.inv.eq_cartesianHom]
    exact CartesianBasedFunctor.Reindex.mapIso.inv.fac (toCartesianBasedFunctor f)
      (Functor.Cleavage.ofIsFibered X.p) (Functor.Cleavage.ofIsFibered Y.p) _ x
  naturality_comp := by
    intro U V W g h
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext x
    change X.p.Fiber (unop U.as) at x
    let F := toCartesianBasedFunctor f
    let χX := Functor.Cleavage.ofIsFibered X.p
    let χY := Functor.Cleavage.ofIsFibered Y.p
    let a := g.as.unop
    let b := h.as.unop
    change
      (CartesianBasedFunctor.Reindex.mapIso F χX χY (b ≫ a) x).inv ≫
          (Functor.Cleavage.Reindex.compIsoApp χY a b ((F.fiberFunctor _).obj x)).hom =
        (F.fiberFunctor _).map (Functor.Cleavage.Reindex.compIsoApp χX a b x).hom ≫
          𝟙 _ ≫
          (CartesianBasedFunctor.Reindex.mapIso F χX χY b ((χX.reindex a).obj x)).inv ≫
          𝟙 _ ≫ (χY.reindex b).map
            (CartesianBasedFunctor.Reindex.mapIso F χX χY a x).inv ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
    let l := (CartesianBasedFunctor.Reindex.mapIso F χX χY (b ≫ a) x).inv ≫
      (Functor.Cleavage.Reindex.compIsoApp χY a b ((F.fiberFunctor _).obj x)).hom
    let r := (F.fiberFunctor _).map (Functor.Cleavage.Reindex.compIsoApp χX a b x).hom ≫
      (CartesianBasedFunctor.Reindex.mapIso F χX χY b ((χX.reindex a).obj x)).inv ≫
      (χY.reindex b).map (CartesianBasedFunctor.Reindex.mapIso F χX χY a x).inv
    letI := l.2
    letI := r.2
    letI : Y.p.IsStronglyCartesian a
        (χY.cartesianHom a ((F.fiberFunctor _).obj x)) :=
      (χY.reindexLift a ((F.fiberFunctor _).obj x)).isStronglyCartesian
    letI : Y.p.IsStronglyCartesian b
        (χY.cartesianHom b ((χY.reindex a).obj ((F.fiberFunctor _).obj x))) :=
      (χY.reindexLift b ((χY.reindex a).obj ((F.fiberFunctor _).obj x))).isStronglyCartesian
    letI : Y.p.IsStronglyCartesian (b ≫ a)
        (χY.cartesianHom b ((χY.reindex a).obj ((F.fiberFunctor _).obj x)) ≫
          χY.cartesianHom a ((F.fiberFunctor _).obj x)) :=
      @Functor.IsStronglyCartesian.comp (Over S) Y.total _ _ Y.p
        _ _ _ _ _ _ b a _ _
        (χY.reindexLift b ((χY.reindex a).obj ((F.fiberFunctor _).obj x))).isStronglyCartesian
        (χY.reindexLift a ((F.fiberFunctor _).obj x)).isStronglyCartesian
    change l = r
    apply Functor.Fiber.hom_ext
    change l.1 = r.1
    apply Functor.IsStronglyCartesian.ext Y.p (b ≫ a)
      (χY.cartesianHom b ((χY.reindex a).obj ((F.fiberFunctor _).obj x)) ≫
        χY.cartesianHom a ((F.fiberFunctor _).obj x)) (𝟙 _)
    change
      ((CartesianBasedFunctor.Reindex.mapIso F χX χY (b ≫ a) x).inv.1 ≫
        (Functor.Cleavage.Reindex.compIsoApp χY a b ((F.fiberFunctor _).obj x)).hom.1) ≫
          (χY.cartesianHom b ((χY.reindex a).obj ((F.fiberFunctor _).obj x)) ≫
            χY.cartesianHom a ((F.fiberFunctor _).obj x)) =
      (F.toFunctor.map (Functor.Cleavage.Reindex.compIsoApp χX a b x).hom.1 ≫
        (CartesianBasedFunctor.Reindex.mapIso F χX χY b ((χX.reindex a).obj x)).inv.1 ≫
        ((χY.reindex b).map (CartesianBasedFunctor.Reindex.mapIso F χX χY a x).inv).1) ≫
          (χY.cartesianHom b ((χY.reindex a).obj ((F.fiberFunctor _).obj x)) ≫
            χY.cartesianHom a ((F.fiberFunctor _).obj x))
    simp only [Category.assoc]
    erw [Functor.Cleavage.Reindex.compIsoApp.hom.fac χY a b ((F.fiberFunctor _).obj x),
      CartesianBasedFunctor.Reindex.mapIso.inv.fac F χX χY (b ≫ a) x,
      ← Category.assoc
        (((χY.reindex b).map (CartesianBasedFunctor.Reindex.mapIso F χX χY a x).inv).1),
      Functor.Cleavage.reindex.map_fac]
    simp only [Category.assoc]
    erw [← Category.assoc
      (CartesianBasedFunctor.Reindex.mapIso F χX χY b ((χX.reindex a).obj x)).inv.1,
      CartesianBasedFunctor.Reindex.mapIso.inv.fac,
      CartesianBasedFunctor.Reindex.mapIso.inv.fac,
      ← F.toFunctor.map_comp, ← F.toFunctor.map_comp]
    erw [Functor.Cleavage.Reindex.compIsoApp.hom.fac χX a b x]

set_option backward.isDefEq.respectTransparency false in
/-- Unlifted isomorphism-presheaf map induced by `f` at a pair of fibre objects. -/
def isomMapHom (f : X ⟶ Y) {T : Over S} (x x' : X.p.Fiber T) :
    Functor.isomorphismPresheaf X.p x x' ⟶
      Functor.isomorphismPresheaf Y.p
        ((fiberFunctor f T).obj x) ((fiberFunctor f T).obj x') where
  app W :=
    TypeCat.ofHom fun φ =>
      ⟨(Pseudofunctor.StrongTrans.presheafHomMap (homStrongTrans f) x x').app W φ.1,
        by
          letI : IsIso φ.1 := φ.2
          let e := Cat.Hom.toNatIso ((homStrongTrans f).naturality (unop W).hom.op.toLoc)
          haveI : IsIso (e.app x).inv := (e.app x).isIso_inv
          haveI : IsIso ((fiberFunctor f (unop W).left).map φ.1) := inferInstance
          haveI : IsIso (e.app x').hom := (e.app x').isIso_hom
          change IsIso
            ((e.app x).inv ≫
              (fiberFunctor f (unop W).left).map φ.1 ≫
                (e.app x').hom)
          infer_instance⟩
  naturality := by
    intro W₁ W₂ g
    ext φ
    apply Subtype.ext
    exact congrArg (fun k => k φ.1)
      ((Pseudofunctor.StrongTrans.presheafHomMap (homStrongTrans f) x x').naturality g)

/-- The map `Isom_X(x, x') ⟶ Isom_Y(f(x), f(x'))` induced by `f`. -/
def isomMap (f : X ⟶ Y) {T : Over S} (x x' : X.p.Fiber T) :
    isom x x' ⟶ isom ((fiberFunctor f T).obj x) ((fiberFunctor f T).obj x') :=
  whiskerRight (isomMapHom f x x') uliftFunctor.{u + 1, u}

/-- Evaluation of `isomMap` on the underlying Hom-presheaf section is the
strong-transformation action. -/
theorem isomMap_apply (f : X ⟶ Y) {T : Over S} (x x' : X.p.Fiber T)
    (W : (Over T)ᵒᵖ) (φ : (isom x x').obj W) :
    ((isomMap f x x').app W φ).down.1 =
      (Pseudofunctor.StrongTrans.presheafHomMap (homStrongTrans f) x x').app W
        φ.down.1 :=
  rfl

/-- Yoneda transpose of a fibrewise isomorphism `α : f(x) ≅ f(x')`, as a map from the
identity slice of `T`. -/
def alphaSection (f : X ⟶ Y) {T : Over S} (x x' : X.p.Fiber T)
    (α : (fiberFunctor f T).obj x ≅ (fiberFunctor f T).obj x') :
    yoneda.obj (Over.mk (𝟙 T)) ⋙ uliftFunctor.{u + 1, u} ⟶
      isom ((fiberFunctor f T).obj x) ((fiberFunctor f T).obj x') :=
  whiskerRight
    (yonedaEquiv.symm
      (⟨(Functor.fiberPseudofunctor Y.p).presheafHomObjHomEquiv α.hom, by
        change IsIso
          (((Cat.Hom.toNatIso ((Functor.fiberPseudofunctor Y.p).mapId
              (.mk (op T)))).app ((fiberFunctor f T).obj x)).hom ≫ α.hom ≫
            ((Cat.Hom.toNatIso ((Functor.fiberPseudofunctor Y.p).mapId
              (.mk (op T)))).app ((fiberFunctor f T).obj x')).inv)
        infer_instance⟩ :
        (Functor.isomorphismPresheaf Y.p ((fiberFunctor f T).obj x)
            ((fiberFunctor f T).obj x')).obj
          (op (Over.mk (𝟙 T)))))
    uliftFunctor.{u + 1, u}

/-- The identity-slice component of `alphaSection` is the packaged isomorphism `α`. -/
theorem alphaSection_app (f : X ⟶ Y) {T : Over S} (x x' : X.p.Fiber T)
    (α : (fiberFunctor f T).obj x ≅ (fiberFunctor f T).obj x') :
    ((alphaSection f x x' α).app (op (Over.mk (𝟙 T)))
        (ULift.up (𝟙 (Over.mk (𝟙 T))))).down.1 =
      (Functor.fiberPseudofunctor Y.p).presheafHomObjHomEquiv α.hom :=
  by
    change ((Functor.isomorphismPresheaf Y.p ((fiberFunctor f T).obj x)
      ((fiberFunctor f T).obj x')).map (𝟙 _) _).1 = _
    rw [Functor.map_id]
    rfl

end CategoryTheory.FiberedCategoryOver.Groupoids.Hom.diagonal
