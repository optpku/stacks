/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Reindex.Chosen.Construction.Basic
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Reindex.Explicit.Construction.Identity
import Mathlib.Tactic.CrossRefAttribute

/-!
# Identity Comparison for Selected Fiber-Pullback Reindexing

This leaf owns the objectwise and natural identity comparisons for selected reindexing of
categorical pullbacks of fibers.
-/

@[expose] public section

open CategoryTheory.Limits
open CategoricalPullback
open Opposite
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor
open scoped CategoricalPullback CategoryTheory.Bicategory

universe u v

namespace CategoryTheory

namespace FiberedCategoryOver.PseudoPullback.reindex.chosen

universe w vT

variable {C : Type u} [Category.{v} C]
variable {X Y S : FiberedCategoryOver.{u, v, w, vT} C}

/-- The objectwise unit comparison from a fiber-pullback object to its selected reindexing along
the identity base arrow. -/
noncomputable def idIsoApp
    (F : X ⟶ S) (G : Y ⟶ S) (U : C)
    (P : (fiberFunctor F U) ⊡ (fiberFunctor G U)) :
    P ≅ (functor F G (𝟙 U)).obj P :=
  BasedCategory.PseudoPullback.reindex.explicit.idIsoApp
    (toCartesianBasedFunctor F) (toCartesianBasedFunctor G)
    X.chosenCleavage Y.chosenCleavage S.chosenCleavage U P

/-- The left component of the forward selected fiber-pullback unit comparison. -/
@[simp]
theorem idIsoApp.hom.fst
    (F : X ⟶ S) (G : Y ⟶ S) (U : C)
    (P : (fiberFunctor F U) ⊡ (fiberFunctor G U)) :
    (idIsoApp F G U P).hom.fst =
      (Functor.Chosen.Reindex.idIsoApp X.p U P.fst).hom := by
  rfl

/-- The right component of the forward selected fiber-pullback unit comparison. -/
@[simp]
theorem idIsoApp.hom.snd
    (F : X ⟶ S) (G : Y ⟶ S) (U : C)
    (P : (fiberFunctor F U) ⊡ (fiberFunctor G U)) :
    (idIsoApp F G U P).hom.snd =
      (Functor.Chosen.Reindex.idIsoApp Y.p U P.snd).hom := by
  rfl

/-- The left component of the inverse selected fiber-pullback unit comparison. -/
@[simp]
theorem idIsoApp.inv.fst
    (F : X ⟶ S) (G : Y ⟶ S) (U : C)
    (P : (fiberFunctor F U) ⊡ (fiberFunctor G U)) :
    (idIsoApp F G U P).inv.fst =
      (Functor.Chosen.Reindex.idIsoApp X.p U P.fst).inv := by
  rfl

/-- The right component of the inverse selected fiber-pullback unit comparison. -/
@[simp]
theorem idIsoApp.inv.snd
    (F : X ⟶ S) (G : Y ⟶ S) (U : C)
    (P : (fiberFunctor F U) ⊡ (fiberFunctor G U)) :
    (idIsoApp F G U P).inv.snd =
      (Functor.Chosen.Reindex.idIsoApp Y.p U P.snd).inv := by
  rfl

private theorem selected_id_inv_naturality
    {T : Type w} [Category.{vT} T] (p : T ⥤ C) [p.IsFibered]
    (U : C) {x y : p.Fiber U} (φ : x ⟶ y) :
    (Functor.Chosen.reindex p (𝟙 U)).map φ ≫
        (Functor.Chosen.Reindex.idIsoApp p U y).inv =
      (Functor.Chosen.Reindex.idIsoApp p U x).inv ≫ φ := by
  let χ := Functor.Cleavage.ofIsFibered p
  have inv_eq (z : p.Fiber U) :
      (Functor.Chosen.Reindex.idIsoApp p U z).inv.1 = χ.cartesianHom (𝟙 U) z := by
    change (Functor.Cleavage.Reindex.idAmbientIso χ U z).inv = _
    letI : p.IsStronglyCartesian (𝟙 U) (χ.cartesianHom (𝟙 U) z) :=
      (χ.reindexLift (𝟙 U) z).isStronglyCartesian
    letI : p.IsStronglyCartesian (𝟙 U) (𝟙 z.1) :=
      Functor.IsHomLift.isStronglyCartesian_of_isIso (𝟙 z : z ⟶ z).2
    letI : p.IsHomLift ((Iso.refl U).inv ≫ (Iso.refl U).hom ≫ 𝟙 U)
        (χ.cartesianHom (𝟙 U) z) := by
      simpa only [Iso.refl_inv, Iso.refl_hom, Category.id_comp] using
        (show p.IsHomLift (𝟙 U) (χ.cartesianHom (𝟙 U) z) from
          (χ.reindexLift (𝟙 U) z).isStronglyCartesian.toIsHomLift)
    have h : (Functor.Cleavage.Reindex.idAmbientIso χ U z).inv ≫ 𝟙 z.1 =
        χ.cartesianHom (𝟙 U) z := by
      dsimp only [Functor.Cleavage.Reindex.idAmbientIso,
        Functor.IsStronglyCartesian.DomainIso.ofBaseIso,
        Functor.IsStronglyCartesian.domainIsoOfBaseIso]
      apply Functor.IsStronglyCartesian.fac
    simpa only [Category.comp_id] using h
  apply Functor.Fiber.hom_ext
  change ((χ.reindex (𝟙 U)).map φ).1 ≫
      (Functor.Chosen.Reindex.idIsoApp p U y).inv.1 =
    (Functor.Chosen.Reindex.idIsoApp p U x).inv.1 ≫ φ.1
  rw [inv_eq, inv_eq]
  letI : p.IsStronglyCartesian (𝟙 U) (χ.cartesianHom (𝟙 U) y) :=
    (χ.reindexLift (𝟙 U) y).isStronglyCartesian
  letI : p.IsHomLift (𝟙 U) (χ.cartesianHom (𝟙 U) x ≫ φ.1) :=
    @IsHomLift.comp_lift_id_right' C T _ _ p U U
      (χ.reindexObj (𝟙 U) x).1 x.1 y.1 (𝟙 U) (χ.cartesianHom (𝟙 U) x)
      (χ.reindexLift (𝟙 U) x).isStronglyCartesian.toIsHomLift U φ.1 φ.2
  exact Functor.IsStronglyCartesian.fac p (𝟙 U) (χ.cartesianHom (𝟙 U) y)
    (Category.id_comp (𝟙 U)).symm (χ.cartesianHom (𝟙 U) x ≫ φ.1)

/-- The selected objectwise fiber-pullback unit comparisons are natural. -/
theorem idIsoApp.naturality.hom
    (F : X ⟶ S) (G : Y ⟶ S) (U : C)
    {P Q : (fiberFunctor F U) ⊡ (fiberFunctor G U)} (φ : P ⟶ Q) :
    φ ≫ (idIsoApp F G U Q).hom =
      (idIsoApp F G U P).hom ≫
        (functor F G (𝟙 U)).map φ := by
  apply CategoricalPullback.hom_ext
  · change φ.fst ≫ (Functor.Chosen.Reindex.idIsoApp X.p U Q.fst).hom =
      (Functor.Chosen.Reindex.idIsoApp X.p U P.fst).hom ≫
        (Functor.Chosen.reindex X.p (𝟙 U)).map φ.fst
    apply (Iso.inv_comp_eq (Functor.Chosen.Reindex.idIsoApp X.p U P.fst)).mp
    rw [← Category.assoc, ← selected_id_inv_naturality X.p U φ.fst,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · change φ.snd ≫ (Functor.Chosen.Reindex.idIsoApp Y.p U Q.snd).hom =
      (Functor.Chosen.Reindex.idIsoApp Y.p U P.snd).hom ≫
        (Functor.Chosen.reindex Y.p (𝟙 U)).map φ.snd
    apply (Iso.inv_comp_eq (Functor.Chosen.Reindex.idIsoApp Y.p U P.snd)).mp
    rw [← Category.assoc, ← selected_id_inv_naturality Y.p U φ.snd,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Inverse naturality of the selected objectwise fiber-pullback unit comparison. -/
theorem idIsoApp.naturality.inv
    (F : X ⟶ S) (G : Y ⟶ S) (U : C)
    {P Q : (fiberFunctor F U) ⊡ (fiberFunctor G U)} (φ : P ⟶ Q) :
    (functor F G (𝟙 U)).map φ ≫
        (idIsoApp F G U Q).inv =
      (idIsoApp F G U P).inv ≫ φ := by
  apply CategoricalPullback.hom_ext
  · exact selected_id_inv_naturality X.p U φ.fst
  · exact selected_id_inv_naturality Y.p U φ.snd

/-- Selected reindexing of a categorical pullback of fibers along the identity is naturally
isomorphic to the identity functor. -/
@[stacks 0040 "selected identity comparison for fiber-pullback reindexing"]
noncomputable def idIso
    (F : X ⟶ S) (G : Y ⟶ S) (U : C) :
    𝟭 ((fiberFunctor F U) ⊡ (fiberFunctor G U)) ≅
      functor F G (𝟙 U) :=
  BasedCategory.PseudoPullback.reindex.explicit.idIso
    (toCartesianBasedFunctor F) (toCartesianBasedFunctor G)
    X.chosenCleavage Y.chosenCleavage S.chosenCleavage U

/-- The first component of the forward selected natural unit comparison. -/
@[simp]
theorem idIso.hom.app.fst
    (F : X ⟶ S) (G : Y ⟶ S) (U : C)
    (P : (fiberFunctor F U) ⊡ (fiberFunctor G U)) :
    ((idIso F G U).hom.app P).fst =
      (Functor.Chosen.Reindex.idIsoApp X.p U P.fst).hom := by
  rfl

/-- The second component of the forward selected natural unit comparison. -/
@[simp]
theorem idIso.hom.app.snd
    (F : X ⟶ S) (G : Y ⟶ S) (U : C)
    (P : (fiberFunctor F U) ⊡ (fiberFunctor G U)) :
    ((idIso F G U).hom.app P).snd =
      (Functor.Chosen.Reindex.idIsoApp Y.p U P.snd).hom := by
  rfl

/-- The first component of the inverse selected natural unit comparison. -/
@[simp]
theorem idIso.inv.app.fst
    (F : X ⟶ S) (G : Y ⟶ S) (U : C)
    (P : (fiberFunctor F U) ⊡ (fiberFunctor G U)) :
    ((idIso F G U).inv.app P).fst =
      (Functor.Chosen.Reindex.idIsoApp X.p U P.fst).inv := by
  rfl

/-- The second component of the inverse selected natural unit comparison. -/
@[simp]
theorem idIso.inv.app.snd
    (F : X ⟶ S) (G : Y ⟶ S) (U : C)
    (P : (fiberFunctor F U) ⊡ (fiberFunctor G U)) :
    ((idIso F G U).inv.app P).snd =
      (Functor.Chosen.Reindex.idIsoApp Y.p U P.snd).inv := by
  rfl

end FiberedCategoryOver.PseudoPullback.reindex.chosen

end CategoryTheory
