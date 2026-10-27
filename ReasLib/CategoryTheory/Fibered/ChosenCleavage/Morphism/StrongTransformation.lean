/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Bicategory.Modification.Pseudo
public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Morphism.Naturality

/-!
# Strong transformations of selected fiber pseudofunctors

A morphism of fibred categories acts on selected fiber pseudofunctors by a
strong transformation.  This module owns that action and its computation and
coherence API.
-/

@[expose] public section

universe u v uS vS

namespace CategoryTheory

open Bicategory Functor Opposite
open scoped CategoryTheory.Bicategory

namespace FiberedCategoryOver

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.{u, v, uS, vS} C}

/-- Naturality of the strong-transformation constraint with respect to a `2`-morphism in the
locally discrete base. -/
theorem strongTrans.naturality₂ (F : X ⟶ Y)
    {a b : LocallyDiscrete Cᵒᵖ} {f g : a ⟶ b} (η : f ⟶ g) :
    (Functor.fiberPseudofunctor X.p).map₂ η ▷
          (fiberFunctor F (unop b.as)).toCatHom ≫
        (Cat.Hom.isoMk (Reindex.pseudonaturalityIso F g.as.unop)).hom =
      (Cat.Hom.isoMk (Reindex.pseudonaturalityIso F f.as.unop)).hom ≫
        (fiberFunctor F (unop a.as)).toCatHom ◁
          (Functor.fiberPseudofunctor Y.p).map₂ η := by
  obtain rfl := LocallyDiscrete.eq_of_hom η
  have hη : η = 𝟙 f := Subsingleton.elim _ _
  subst η
  change 𝟙 _ ▷ _ ≫ _ = _ ≫ _ ◁ 𝟙 _
  simp

/-- Identity coherence for the strong transformation induced by a morphism of fibred categories. -/
theorem strongTrans.naturality.id (F : X ⟶ Y) (a : LocallyDiscrete Cᵒᵖ) :
    (Cat.Hom.isoMk
          (Reindex.pseudonaturalityIso F ((𝟙 a : a ⟶ a).as.unop))).hom ≫
        (fiberFunctor F (unop a.as)).toCatHom ◁
          ((Functor.fiberPseudofunctor Y.p).mapId a).hom =
      ((Functor.fiberPseudofunctor X.p).mapId a).hom ▷
          (fiberFunctor F (unop a.as)).toCatHom ≫
        (λ_ ((fiberFunctor F (unop a.as)).toCatHom)).hom ≫
          (ρ_ ((fiberFunctor F (unop a.as)).toCatHom)).inv := by
  ext x
  change (Reindex.mapIso F (𝟙 (unop a.as)) x).inv ≫
      (Functor.Chosen.Reindex.idIsoApp Y.p (unop a.as)
        ((fiberFunctor F (unop a.as)).obj x)).inv =
    (fiberFunctor F (unop a.as)).map
      (Functor.Chosen.Reindex.idIsoApp X.p (unop a.as) x).inv ≫ 𝟙 _ ≫ 𝟙 _
  simp only [Category.comp_id]
  apply Subtype.ext
  change (Reindex.mapIso F (𝟙 (unop a.as)) x).inv.1 ≫
      (Functor.Chosen.Reindex.idIsoApp Y.p (unop a.as)
        ((fiberFunctor F (unop a.as)).obj x)).inv.1 =
    (toFunctor F).map (Functor.Chosen.Reindex.idIsoApp X.p (unop a.as) x).inv.1
  erw [Functor.Chosen.Reindex.idIsoApp.inv.eq_cartesianHom,
    Functor.Chosen.Reindex.idIsoApp.inv.eq_cartesianHom]
  exact Reindex.mapIso.inv.fac F (𝟙 (unop a.as)) x

/-- Composition coherence for the strong transformation induced by a morphism of fibred
categories. -/
theorem strongTrans.naturality.comp (F : X ⟶ Y)
    {a b c : LocallyDiscrete Cᵒᵖ} (f : a ⟶ b) (g : b ⟶ c) :
    (Cat.Hom.isoMk (Reindex.pseudonaturalityIso F (f ≫ g).as.unop)).hom ≫
        (fiberFunctor F (unop a.as)).toCatHom ◁
          ((Functor.fiberPseudofunctor Y.p).mapComp f g).hom =
      ((Functor.fiberPseudofunctor X.p).mapComp f g).hom ▷
          (fiberFunctor F (unop c.as)).toCatHom ≫
        (α_ _ _ _).hom ≫
          (Functor.fiberPseudofunctor X.p).map f ◁
            (Cat.Hom.isoMk (Reindex.pseudonaturalityIso F g.as.unop)).hom ≫
          (α_ _ _ _).inv ≫
            (Cat.Hom.isoMk (Reindex.pseudonaturalityIso F f.as.unop)).hom ▷
              (Functor.fiberPseudofunctor Y.p).map g ≫
            (α_ _ _ _).hom := by
  ext x
  change (Reindex.mapIso F (g.as.unop ≫ f.as.unop) x).inv ≫
      (Functor.Chosen.Reindex.compIsoApp Y.p f.as.unop g.as.unop
        ((fiberFunctor F (unop a.as)).obj x)).hom =
    (fiberFunctor F (unop c.as)).map
      (Functor.Chosen.Reindex.compIsoApp X.p f.as.unop g.as.unop x).hom ≫
      𝟙 _ ≫ (Reindex.mapIso F g.as.unop
        ((Functor.Chosen.reindex X.p f.as.unop).obj x)).inv ≫
      𝟙 _ ≫ (Functor.Chosen.reindex Y.p g.as.unop).map
        (Reindex.mapIso F f.as.unop x).inv ≫ 𝟙 _
  simp only [Category.comp_id, Category.id_comp]
  have h := CartesianBasedFunctor.Reindex.mapIso.specifiedComp.inv
    (toCartesianBasedFunctor F) X.chosenCleavage Y.chosenCleavage
    f.as.unop g.as.unop (g.as.unop ≫ f.as.unop) rfl x
  simp only [Functor.Cleavage.Reindex.specifiedCompIsoApp,
    Functor.Cleavage.Reindex.congrIsoApp, eqToIso_refl, Iso.refl_inv,
    Iso.trans_inv, Category.comp_id] at h
  change (Reindex.mapIso F g.as.unop ((Functor.Chosen.reindex X.p f.as.unop).obj x)).inv ≫
      (Functor.Chosen.reindex Y.p g.as.unop).map (Reindex.mapIso F f.as.unop x).inv ≫
      (Functor.Chosen.Reindex.compIsoApp Y.p f.as.unop g.as.unop
        ((fiberFunctor F (unop a.as)).obj x)).inv =
    (fiberFunctor F (unop c.as)).map
      (Functor.Chosen.Reindex.compIsoApp X.p f.as.unop g.as.unop x).inv ≫
      (Reindex.mapIso F (g.as.unop ≫ f.as.unop) x).inv at h
  apply (cancel_mono (Functor.Chosen.Reindex.compIsoApp Y.p f.as.unop g.as.unop
    ((fiberFunctor F (unop a.as)).obj x)).inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [h]
  rw [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id, Functor.map_id,
    Category.id_comp]

/-- A morphism of fibred categories induces a strong transformation between the selected fiber
pseudofunctors. Its components are the intrinsic fiber functors and its naturality constraints are
the selected-cleavage reindexing comparisons. -/
noncomputable def strongTrans (F : X ⟶ Y) :
    Pseudofunctor.StrongTrans (Functor.fiberPseudofunctor X.p)
      (Functor.fiberPseudofunctor Y.p) where
  app U := (fiberFunctor F (unop U.as)).toCatHom
  naturality f := Cat.Hom.isoMk (Reindex.pseudonaturalityIso F f.as.unop)
  naturality_naturality η := strongTrans.naturality₂ F η
  naturality_id a := strongTrans.naturality.id F a
  naturality_comp f g := strongTrans.naturality.comp F f g

/-- The component of `strongTrans F` at a base object is the functor induced by `F` on the
corresponding standard fiber. -/
@[simp]
theorem strongTrans.app (F : X ⟶ Y) (U : LocallyDiscrete Cᵒᵖ) :
    (strongTrans F).app U = (fiberFunctor F (unop U.as)).toCatHom := by
  rfl

/-- The naturality isomorphism of `strongTrans F` is the Cat-bundled selected-cleavage
comparison. -/
@[simp]
theorem strongTrans.naturality (F : X ⟶ Y)
    {U V : LocallyDiscrete Cᵒᵖ} (f : U ⟶ V) :
    (strongTrans F).naturality f =
      Cat.Hom.isoMk (Reindex.pseudonaturalityIso F f.as.unop) := by
  rfl

/-- The functor underlying the component of the induced strong transformation is the canonical
functor between the corresponding standard fibers. -/
@[simp]
theorem strongTrans.app.toFunctor (F : X ⟶ Y) (U : LocallyDiscrete Cᵒᵖ) :
    ((strongTrans F).app U).toFunctor =
      fiberFunctor F (unop U.as) := by
  rfl

/-- The identity morphism of a fibred category induces the identity strong transformation of its
selected fiber pseudofunctor. -/
@[simp]
theorem strongTrans.id (X : FiberedCategoryOver.{u, v, uS, vS} C) :
    strongTrans (𝟙 X) =
      Pseudofunctor.StrongTrans.id
        (Functor.fiberPseudofunctor X.p) := by
  unfold strongTrans Pseudofunctor.StrongTrans.id
  congr 1
  funext a b f
  apply Iso.ext
  ext x
  change (Reindex.mapIso (𝟙 X) f.as.unop x).inv = 𝟙 _ ≫ 𝟙 _
  have h := CartesianBasedFunctor.Reindex.mapIso.id X.chosenCleavage f.as.unop x
  change Reindex.mapIso (𝟙 X) f.as.unop x = _ at h
  rw [h]
  simp
  rfl

/-- Passage from morphisms of fibred categories to selected-fiber strong transformations
preserves composition. -/
@[simp]
theorem strongTrans.comp
    {Z : FiberedCategoryOver.{u, v, uS, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) :
    strongTrans (F ≫ G) =
      Pseudofunctor.StrongTrans.vcomp
        (strongTrans F) (strongTrans G) := by
  unfold strongTrans Pseudofunctor.StrongTrans.vcomp Pseudofunctor.StrongTrans.mkOfOplax
    Oplax.StrongTrans.vcomp Oplax.StrongTrans.mkOfOplax
  congr 1
  funext a b f
  apply Iso.ext
  ext x
  change (Reindex.mapIso (F ≫ G) f.as.unop x).inv =
    𝟙 _ ≫ (fiberFunctor G (unop b.as)).map (Reindex.mapIso F f.as.unop x).inv ≫
      𝟙 _ ≫ (Reindex.mapIso G f.as.unop ((fiberFunctor F (unop a.as)).obj x)).inv ≫ 𝟙 _
  simp only [Category.id_comp, Category.comp_id]
  exact CartesianBasedFunctor.Reindex.mapIso.comp.inv
    (toCartesianBasedFunctor F) (toCartesianBasedFunctor G)
    X.chosenCleavage Y.chosenCleavage Z.chosenCleavage f.as.unop x

/-- Objectwise, the forward strong-transformation constraint is the inverse selected reindexing
comparison. -/
@[simp]
theorem strongTrans.naturality.hom.app (F : X ⟶ Y)
    {U V : LocallyDiscrete Cᵒᵖ} (f : U ⟶ V)
    (x : X.p.Fiber (unop U.as)) :
    ((strongTrans F).naturality f).hom.toNatTrans.app x =
      (Reindex.mapIso F f.as.unop x).inv := by
  rfl

/-- Objectwise, the inverse strong-transformation constraint is the forward selected reindexing
comparison. -/
@[simp]
theorem strongTrans.naturality.inv.app (F : X ⟶ Y)
    {U V : LocallyDiscrete Cᵒᵖ} (f : U ⟶ V)
    (x : X.p.Fiber (unop U.as)) :
    ((strongTrans F).naturality f).inv.toNatTrans.app x =
      (Reindex.mapIso F f.as.unop x).hom := by
  rfl

end FiberedCategoryOver

end CategoryTheory
