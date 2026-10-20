/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Functoriality.Comparison
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Functoriality.Map.Projection
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Cospan.Basic.Modification
import Mathlib.Tactic.CrossRefAttribute

/-!
# Modification action on explicit pseudo-pullbacks

This leaf owns the `2`-cell action sending a modification of based cospan transformations to the
corresponding based natural transformation between explicit pseudo-pullback maps, including its
projection and vertical-composition formulas.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open BasedFunctor
open BasedNatIso
open Functor.IsHomLift
open Functor.Fiber
open CategoricalPullback
open scoped CategoricalPullback
open scoped Bicategory BasedFunctor

universe u v
universe uX₁ vX₁ uY₁ vY₁ uS₁ vS₁
universe uX₂ vX₂ uY₂ vY₂ uS₂ vS₂

namespace CategoryTheory

open Bicategory

namespace BasedCategory

variable {C : Type u} [Category.{v} C]

namespace PseudoPullback

noncomputable section

variable {X₁ : BasedCategory.{vX₁, uX₁} C}
variable {Y₁ : BasedCategory.{vY₁, uY₁} C}
variable {S₁ : BasedCategory.{vS₁, uS₁} C}
variable {X₂ : BasedCategory.{vX₂, uX₂} C}
variable {Y₂ : BasedCategory.{vY₂, uY₂} C}
variable {S₂ : BasedCategory.{vS₂, uS₂} C}
variable {F₁ : X₁ ⥤ᵇ S₁} {G₁ : Y₁ ⥤ᵇ S₁}
variable {F₂ : X₂ ⥤ᵇ S₂} {G₂ : Y₂ ⥤ᵇ S₂}

/-- The left component of a cospan modification is vertical over the common base object of a
pseudo-pullback object. -/
theorem map₂.component.fst.isHomLift
    {ψ φ : BasedCospanTransform F₁ G₁ F₂ G₂}
    (Γ : BasedCospanTransform.Hom ψ φ)
    (P : (PseudoPullback F₁ G₁).obj) :
    X₂.p.IsHomLift (𝟙 (baseObj P))
      (Γ.left.toNatTrans.app (fstObj P)) := sorry

/-- The right component of a cospan modification is vertical over the common base object of a
pseudo-pullback object. -/
theorem map₂.component.snd.isHomLift
    {ψ φ : BasedCospanTransform F₁ G₁ F₂ G₂}
    (Γ : BasedCospanTransform.Hom ψ φ)
    (P : (PseudoPullback F₁ G₁).obj) :
    Y₂.p.IsHomLift (𝟙 (baseObj P))
      (Γ.right.toNatTrans.app (sndObj P)) := sorry

/-- The endpoint components of a modification between cospan transformations commute with the
two mapped pseudo-pullback comparisons. -/
theorem map₂.component.comm
    {ψ φ : BasedCospanTransform F₁ G₁ F₂ G₂}
    (Γ : BasedCospanTransform.Hom ψ φ)
    (P : (PseudoPullback F₁ G₁).obj) :
    CommSq
      (F₂.toFunctor.map
        (Γ.left.toNatTrans.app (fstObj P)))
      (comparison ((map ψ).obj P))
      (comparison ((map φ).obj P))
      (G₂.toFunctor.map
        (Γ.right.toNatTrans.app (sndObj P))) := sorry

/-- The component at a pseudo-pullback object of the `2`-morphism induced by a modification of
cospans. Its base map is the identity and its two component arrows are the corresponding
modification components. -/
def map₂.component
    {ψ φ : BasedCospanTransform F₁ G₁ F₂ G₂}
    (Γ : BasedCospanTransform.Hom ψ φ)
    (P : (PseudoPullback F₁ G₁).obj) :
    (map ψ).obj P ⟶ (map φ).obj P :=
  PseudoPullback.Hom.mk (𝟙 (baseObj P))
    (Γ.left.toNatTrans.app (fstObj P))
    (map₂.component.fst.isHomLift Γ P)
    (Γ.right.toNatTrans.app (sndObj P))
    (map₂.component.snd.isHomLift Γ P) (map₂.component.comm Γ P)

/-- The explicit pseudo-pullback components induced by a cospan modification are natural in
pseudo-pullback morphisms. -/
theorem map₂.component.naturality
    {ψ φ : BasedCospanTransform F₁ G₁ F₂ G₂}
    (Γ : BasedCospanTransform.Hom ψ φ)
    {P Q : (PseudoPullback F₁ G₁).obj} (χ : P ⟶ Q) :
    (map ψ).map χ ≫ map₂.component Γ Q =
      map₂.component Γ P ≫ (map φ).map χ := sorry

/-- The natural transformation between explicit pseudo-pullback maps induced by a modification
of cospans. -/
def map₂.natTrans
    {ψ φ : BasedCospanTransform F₁ G₁ F₂ G₂}
    (Γ : BasedCospanTransform.Hom ψ φ) :
    (map ψ).toFunctor ⟶ (map φ).toFunctor where
  app := map₂.component Γ
  naturality := fun {_ _} χ ↦ map₂.component.naturality Γ χ

/-- Every component of the natural transformation induced by a cospan modification is vertical
over the unchanged common base. -/
theorem map₂.component.isHomLift
    {ψ φ : BasedCospanTransform F₁ G₁ F₂ G₂}
    (Γ : BasedCospanTransform.Hom ψ φ)
    (P : (PseudoPullback F₁ G₁).obj) :
    (PseudoPullback F₂ G₂).p.IsHomLift
      (𝟙 ((PseudoPullback F₁ G₁).p.obj P)) (map₂.component Γ P) := sorry

/-- A modification between cospan transformations induces a based natural transformation
between the corresponding explicit pseudo-pullback maps. -/
@[stacks 0040 "modification action on maps of explicit pseudo-pullbacks"]
def map₂
    {ψ φ : BasedCospanTransform F₁ G₁ F₂ G₂}
    (Γ : BasedCospanTransform.Hom ψ φ) :
    map ψ ⟶ map φ where
  toNatTrans := map₂.natTrans Γ
  isHomLift' := map₂.component.isHomLift Γ

/-- The underlying natural transformation of `map₂ Γ` is its explicit componentwise
construction. -/
@[simp]
theorem map₂.toNatTrans
    {ψ φ : BasedCospanTransform F₁ G₁ F₂ G₂}
    (Γ : BasedCospanTransform.Hom ψ φ) :
    (map₂ Γ).toNatTrans = map₂.natTrans Γ := sorry

/-- The component of the induced based natural transformation is the explicit
cospan-modification component. -/
@[simp]
theorem map₂.app
    {ψ φ : BasedCospanTransform F₁ G₁ F₂ G₂}
    (Γ : BasedCospanTransform.Hom ψ φ)
    (P : (PseudoPullback F₁ G₁).obj) :
    (map₂ Γ).toNatTrans.app P = map₂.component Γ P := sorry

/-- The base component of the induced pseudo-pullback `2`-morphism is the identity. -/
@[simp]
theorem map₂.base
    {ψ φ : BasedCospanTransform F₁ G₁ F₂ G₂}
    (Γ : BasedCospanTransform.Hom ψ φ)
    (P : (PseudoPullback F₁ G₁).obj) :
    baseMap ((map₂ Γ).toNatTrans.app P) =
      𝟙 (baseObj P) := sorry

/-- The first component of the induced pseudo-pullback `2`-morphism is the left component of the
cospan modification. -/
@[simp]
theorem map₂.fst
    {ψ φ : BasedCospanTransform F₁ G₁ F₂ G₂}
    (Γ : BasedCospanTransform.Hom ψ φ)
    (P : (PseudoPullback F₁ G₁).obj) :
    fstMap ((map₂ Γ).toNatTrans.app P) =
      Γ.left.toNatTrans.app (fstObj P) := sorry

/-- The second component of the induced pseudo-pullback `2`-morphism is the right component of
the cospan modification. -/
@[simp]
theorem map₂.snd
    {ψ φ : BasedCospanTransform F₁ G₁ F₂ G₂}
    (Γ : BasedCospanTransform.Hom ψ φ)
    (P : (PseudoPullback F₁ G₁).obj) :
    sndMap ((map₂ Γ).toNatTrans.app P) =
      Γ.right.toNatTrans.app (sndObj P) := sorry

/-- Naturality of the induced `2`-morphism, exposed at the explicit pseudo-pullback owner. -/
@[reassoc]
theorem map₂.naturality
    {ψ φ : BasedCospanTransform F₁ G₁ F₂ G₂}
    (Γ : BasedCospanTransform.Hom ψ φ)
    {P Q : (PseudoPullback F₁ G₁).obj} (χ : P ⟶ Q) :
    (map ψ).map χ ≫ (map₂ Γ).toNatTrans.app Q =
      (map₂ Γ).toNatTrans.app P ≫ (map φ).map χ := sorry

/-- The first projection comparison is `2`-natural in modifications of cospan
transformations. -/
theorem map₂.fstCommutes
    {ψ φ : BasedCospanTransform F₁ G₁ F₂ G₂}
    (Γ : BasedCospanTransform.Hom ψ φ) :
    BasedCategory.whiskerRight (map₂ Γ)
        (CategoryTheory.BasedCategory.PseudoPullback.fst F₂ G₂) ≫
        (map.fstIso φ).hom =
      (map.fstIso ψ).hom ≫
        BasedCategory.whiskerLeft (CategoryTheory.BasedCategory.PseudoPullback.fst F₁ G₁)
          Γ.left := sorry

/-- The second projection comparison is `2`-natural in modifications of cospan
transformations. -/
theorem map₂.sndCommutes
    {ψ φ : BasedCospanTransform F₁ G₁ F₂ G₂}
    (Γ : BasedCospanTransform.Hom ψ φ) :
    BasedCategory.whiskerRight (map₂ Γ)
        (CategoryTheory.BasedCategory.PseudoPullback.snd F₂ G₂) ≫
        (map.sndIso φ).hom =
      (map.sndIso ψ).hom ≫
        BasedCategory.whiskerLeft (CategoryTheory.BasedCategory.PseudoPullback.snd F₁ G₁)
          Γ.right := sorry

/-- The explicit pseudo-pullback action sends the identity cospan modification to the identity
based natural transformation. -/
@[simp]
theorem map₂.id
    (ψ : BasedCospanTransform F₁ G₁ F₂ G₂) :
    map₂ (BasedCospanTransform.Hom.id ψ) = 𝟙 (map ψ) := sorry

/-- The explicit pseudo-pullback action preserves vertical composition of cospan
modifications. -/
@[simp]
theorem map₂.comp
    {ψ φ χ : BasedCospanTransform F₁ G₁ F₂ G₂}
    (Γ : BasedCospanTransform.Hom ψ φ)
    (Δ : BasedCospanTransform.Hom φ χ) :
    map₂ (BasedCospanTransform.Hom.comp Γ Δ) =
      map₂ Γ ≫ map₂ Δ := sorry

end

end PseudoPullback

end BasedCategory

end CategoryTheory
