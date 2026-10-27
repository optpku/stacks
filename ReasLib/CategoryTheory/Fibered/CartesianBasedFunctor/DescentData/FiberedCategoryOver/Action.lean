/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.IndexedFunctor.FiberedCategoryOver.NatTrans
public import ReasLib.CategoryTheory.Sites.Descent.IndexedFunctor.DescentData.Canonical

/-!
# Descent-data action of fibred-category morphisms

This module provides the direct selected-fiber descent-data action of morphisms and
`2`-morphisms of fibred categories, together with its canonical-descent comparison.
-/

@[expose] public section

universe t uC vC uS₁ vS₁

namespace CategoryTheory

open Functor Opposite
open scoped CategoryTheory.Bicategory

namespace FiberedCategoryOver.Descent

variable {C : Type uC} [Category.{vC} C]
variable {A B : FiberedCategoryOver.{uC, vC, uS₁, vS₁} C}
variable {ι : Type t} {S : C} {X : ι → C} (a : ∀ i, X i ⟶ S)

/-- The direct functor on selected-fiber descent data induced by a morphism of fibred categories.
This is the shortest application-facing entry point. -/
noncomputable def functor (F : A ⟶ B) :
    (Functor.fiberPseudofunctor A.p).DescentData a ⥤
      (Functor.fiberPseudofunctor B.p).DescentData a :=
  (Indexed.functor F).mapDescentData a

/-- A fibred-category morphism acts on descent-data objects componentwise through its fiber
functors. -/
@[simp]
theorem functor.obj
    (F : A ⟶ B)
    (D : (Functor.fiberPseudofunctor A.p).DescentData a) (i : ι) :
    ((functor a F).obj D).obj i =
      (fiberFunctor F (X i)).obj (D.obj i) := rfl

/-- A fibred-category morphism transports descent overlap morphisms by its selected reindexing
comparisons. -/
@[simp]
theorem functor.obj.hom
    (F : A ⟶ B)
    (D : (Functor.fiberPseudofunctor A.p).DescentData a)
    ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄
    (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ a i₁ = q) (hf₂ : f₂ ≫ a i₂ = q) :
    ((functor a F).obj D).hom q f₁ f₂ hf₁ hf₂ =
      (Reindex.mapIso F f₁ (D.obj i₁)).hom ≫
        (fiberFunctor F Y).map (D.hom q f₁ f₂ hf₁ hf₂) ≫
      (Reindex.mapIso F f₂ (D.obj i₂)).inv := rfl

/-- Total-category readout of the direct overlap-morphism computation. -/
@[simp]
theorem functor.obj.hom.val
    (F : A ⟶ B)
    (D : (Functor.fiberPseudofunctor A.p).DescentData a)
    ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄
    (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ a i₁ = q) (hf₂ : f₂ ≫ a i₂ = q) :
    (((functor a F).obj D).hom
        q f₁ f₂ hf₁ hf₂).1 =
      (Reindex.mapIso F f₁ (D.obj i₁)).hom.1 ≫
        ((fiberFunctor F Y).map (D.hom q f₁ f₂ hf₁ hf₂)).1 ≫
      (Reindex.mapIso F f₂ (D.obj i₂)).inv.1 := rfl

/-- A fibred-category morphism acts on descent-data morphisms componentwise through its fiber
functors. -/
@[simp]
theorem functor.map.hom
    (F : A ⟶ B)
    {D₁ D₂ : (Functor.fiberPseudofunctor A.p).DescentData a}
    (φ : D₁ ⟶ D₂) (i : ι) :
    ((functor a F).map φ).hom i =
      (fiberFunctor F (X i)).map (φ.hom i) := rfl

/-- Total-category readout of the direct descent-morphism computation. -/
@[simp]
theorem functor.map.hom.val
    (F : A ⟶ B)
    {D₁ D₂ : (Functor.fiberPseudofunctor A.p).DescentData a}
    (φ : D₁ ⟶ D₂) (i : ι) :
    (((functor a F).map φ).hom i).1 =
      ((fiberFunctor F (X i)).map (φ.hom i)).1 := rfl

/-- The direct descent-data functor of the identity fibred-category morphism is the identity
functor. -/
@[simp]
theorem functor.id
    (A : FiberedCategoryOver.{uC, vC, uS₁, vS₁} C) :
    functor a (𝟙 A) =
      𝟭 ((Functor.fiberPseudofunctor A.p).DescentData a) := by
  simp only [functor, Indexed.functor.id,
    Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor.mapDescentData.id]

/-- The direct descent-data functor of a composite fibred-category morphism is successive
transport through its factors. -/
@[simp]
theorem functor.comp
    {D : FiberedCategoryOver.{uC, vC, uS₁, vS₁} C}
    (F : A ⟶ B) (G : B ⟶ D) :
    functor a (F ≫ G) =
      functor a F ⋙ functor a G := by
  simp only [functor, Indexed.functor.comp,
    Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor.mapDescentData.comp]

/-- A `2`-morphism of fibred-category morphisms induces a natural transformation between their
direct descent-data functors. -/
noncomputable def cell
    {F G : A ⟶ B} (τ : F ⟶ G) :
    functor a F ⟶ functor a G :=
  Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor.mapDescentData.natTrans
    a (Indexed.cell τ)

/-- Components of the natural transformation on direct descent data are the restricted fiber
components of the original `2`-morphism. -/
@[simp]
theorem cell.component
    {F G : A ⟶ B} (τ : F ⟶ G)
    (D : (Functor.fiberPseudofunctor A.p).DescentData a) (i : ι) :
    ((cell a τ).app D).hom i =
      (fiberNatTrans τ (X i)).app (D.obj i) := rfl

/-- Forgetting a component of the natural transformation on direct descent data recovers the
underlying total-category component. -/
@[simp]
theorem cell.component.val
    {F G : A ⟶ B} (τ : F ⟶ G)
    (D : (Functor.fiberPseudofunctor A.p).DescentData a) (i : ι) :
    (((cell a τ).app D).hom i).1 =
      τ.hom.toNatTrans.app (D.obj i).1 := rfl

/-- Passage from a `2`-identity to direct descent data is the identity natural
transformation. -/
@[simp]
theorem cell.id
    (F : A ⟶ B) :
    cell a (𝟙 F) =
      𝟙 (functor a F) := by
  apply NatTrans.ext
  funext D
  exact Pseudofunctor.DescentData.hom_ext (fun i ↦ rfl)

/-- Passage to direct descent data preserves vertical composition of `2`-morphisms. -/
@[simp]
theorem cell.comp
    {F G H : A ⟶ B} (τ : F ⟶ G) (σ : G ⟶ H) :
    cell a (τ ≫ σ) =
      cell a τ ≫ cell a σ := by
  apply NatTrans.ext
  funext D
  exact Pseudofunctor.DescentData.hom_ext (fun i ↦ rfl)

/-- The direct descent-data action of a `2`-morphism is natural in descent-data morphisms. -/
theorem cell.naturality
    {F G : A ⟶ B} (τ : F ⟶ G)
    {D₁ D₂ : (Functor.fiberPseudofunctor A.p).DescentData a}
    (φ : D₁ ⟶ D₂) :
    (functor a F).map φ ≫ (cell a τ).app D₂ =
      (cell a τ).app D₁ ≫ (functor a G).map φ := by
  apply Pseudofunctor.DescentData.hom_ext
  intro i
  apply Subtype.ext
  exact τ.hom.toNatTrans.naturality (φ.hom i).1

variable (A B) in
/-- For fixed fibred source and target, passage to direct descent-data functors is functorial on
the hom-category.

The endpoints are explicit because the indexing family does not determine the fixed source and
target fibred categories. -/
noncomputable def homFunctor :
    (A ⟶ B) ⥤
      ((Functor.fiberPseudofunctor A.p).DescentData a ⥤
        (Functor.fiberPseudofunctor B.p).DescentData a) :=
  Indexed.homFunctor A B ⋙
    Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor.mapDescentData.functor a

/-- The object action of the descent-data hom-functor is `Descent.functor`. -/
@[simp]
theorem homFunctor.obj
    (F : A ⟶ B) :
    (homFunctor A B a).obj F =
      FiberedCategoryOver.Descent.functor a F := rfl

/-- The morphism action of the descent-data hom-functor is `Descent.cell`. -/
@[simp]
theorem homFunctor.map
    {F G : A ⟶ B} (τ : F ⟶ G) :
    (homFunctor A B a).map τ =
      cell a τ := rfl

/-- Canonical descent commutes with the direct descent-data functor of a fibred-category
morphism. -/
noncomputable def comparisonIso
    (F : A ⟶ B) :
    (Functor.fiberPseudofunctor A.p).toDescentData a ⋙
        functor a F ≅
      fiberFunctor F S ⋙
        (Functor.fiberPseudofunctor B.p).toDescentData a :=
  Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor.Canonical.Comparison.iso
    (Indexed.functor F) a

/-- Components of the direct canonical-descent comparison are inverse selected reindexing
comparisons. -/
@[simp]
theorem comparisonIso.hom.component
    (F : A ⟶ B) (x : A.p.Fiber S) (i : ι) :
    ((comparisonIso a F).hom.app x).hom i =
      (Reindex.mapIso F (a i) x).inv := rfl

/-- Total-category readout of a forward direct canonical-descent comparison component. -/
@[simp]
theorem comparisonIso.hom.component.val
    (F : A ⟶ B) (x : A.p.Fiber S) (i : ι) :
    (((comparisonIso a F).hom.app x).hom i).1 =
      (Reindex.mapIso F (a i) x).inv.1 := rfl

/-- Inverse components of the direct canonical-descent comparison are forward selected
reindexing comparisons. -/
@[simp]
theorem comparisonIso.inv.component
    (F : A ⟶ B) (x : A.p.Fiber S) (i : ι) :
    ((comparisonIso a F).inv.app x).hom i =
      (Reindex.mapIso F (a i) x).hom := rfl

/-- Total-category readout of an inverse direct canonical-descent comparison component. -/
@[simp]
theorem comparisonIso.inv.component.val
    (F : A ⟶ B) (x : A.p.Fiber S) (i : ι) :
    (((comparisonIso a F).inv.app x).hom i).1 =
      (Reindex.mapIso F (a i) x).hom.1 := rfl

/-- The direct canonical-descent comparison is natural in `2`-morphisms of fibred-category
morphisms. -/
theorem comparisonIso.hom.naturality
    {F G : A ⟶ B} (τ : F ⟶ G) (x : A.p.Fiber S) :
    (comparisonIso a F).hom.app x ≫
        ((Functor.fiberPseudofunctor B.p).toDescentData a).map
          ((fiberNatTrans τ S).app x) =
      (cell a τ).app
          (((Functor.fiberPseudofunctor A.p).toDescentData a).obj x) ≫
        (comparisonIso a G).hom.app x := by
  apply Pseudofunctor.DescentData.hom_ext
  intro i
  exact (Indexed.cell τ).naturality (a i) x

/-- Inverse form of naturality of the direct canonical-descent comparison in a
fibred-category `2`-morphism. -/
theorem comparisonIso.inv.naturality
    {F G : A ⟶ B} (τ : F ⟶ G) (x : A.p.Fiber S) :
    ((Functor.fiberPseudofunctor B.p).toDescentData a).map
          ((fiberNatTrans τ S).app x) ≫
        (comparisonIso a G).inv.app x =
      (comparisonIso a F).inv.app x ≫
        (cell a τ).app
          (((Functor.fiberPseudofunctor A.p).toDescentData a).obj x) := by
  apply (Iso.comp_inv_eq ((comparisonIso a G).app x)).2
  have h := (Iso.inv_comp_eq ((comparisonIso a F).app x)).2
    (comparisonIso.hom.naturality a τ x).symm
  exact h.symm.trans (Category.assoc _ _ _).symm

end FiberedCategoryOver.Descent

end CategoryTheory
