/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Morphism.StrongTransformation

/-!
# Modifications of selected fiber strong transformations

This module lifts `2`-morphisms of fibred-category morphisms to modifications
between their induced selected-fiber strong transformations.
-/

@[expose] public section

universe u v uS vS

namespace CategoryTheory

open Bicategory Functor Opposite
open scoped CategoryTheory.Bicategory

namespace FiberedCategoryOver

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.{u, v, uS, vS} C}
variable {F G : X ⟶ Y}

/-- Naturality required to package the fiber restrictions of a `2`-morphism as a modification of
the induced strong transformations. -/
theorem strongTrans₂.naturality (τ : F ⟶ G)
    {a b : LocallyDiscrete Cᵒᵖ} (f : a ⟶ b) :
    (Functor.fiberPseudofunctor X.p).map f ◁
          (fiberNatTrans τ (unop b.as)).toCatHom₂ ≫
          (Cat.Hom.isoMk (Reindex.pseudonaturalityIso G f.as.unop)).hom =
      (Cat.Hom.isoMk (Reindex.pseudonaturalityIso F f.as.unop)).hom ≫
        (fiberNatTrans τ (unop a.as)).toCatHom₂ ▷
          (Functor.fiberPseudofunctor Y.p).map f := sorry

/-- A `2`-morphism of fibred-category morphisms induces a modification between the corresponding
strong transformations of selected fiber pseudofunctors. -/
def strongTrans₂ (τ : F ⟶ G) :
    Pseudofunctor.StrongTrans.Modification
      (strongTrans F) (strongTrans G) where
  app U := (fiberNatTrans τ (unop U.as)).toCatHom₂
  naturality f := strongTrans₂.naturality τ f

/-- The component of `strongTrans₂ τ` is the Cat-bundled restriction of `τ` to the
corresponding standard fiber. -/
@[simp]
theorem strongTrans₂.app (τ : F ⟶ G) (U : LocallyDiscrete Cᵒᵖ) :
    (strongTrans₂ τ).app U =
      (fiberNatTrans τ (unop U.as)).toCatHom₂ := sorry

/-- The objectwise component of the induced modification is the corresponding component of the
restricted owner `2`-morphism. -/
@[simp]
theorem strongTrans₂.app.component (τ : F ⟶ G) (U : LocallyDiscrete Cᵒᵖ)
    (x : X.p.Fiber (unop U.as)) :
    ((strongTrans₂ τ).app U).toNatTrans.app x =
      (fiberNatTrans τ (unop U.as)).app x := sorry

/-- The total-category arrow underlying a modification component is the original owner
`2`-morphism component. -/
@[simp]
theorem strongTrans₂.app.component.val (τ : F ⟶ G) (U : LocallyDiscrete Cᵒᵖ)
    (x : X.p.Fiber (unop U.as)) :
    (((strongTrans₂ τ).app U).toNatTrans.app x).1 =
      τ.hom.toNatTrans.app x.1 := sorry

/-- Two induced modifications agree when all of their base-object components agree. -/
theorem strongTrans₂.ext {τ σ : F ⟶ G}
    (h : ∀ U : LocallyDiscrete Cᵒᵖ,
      (strongTrans₂ τ).app U = (strongTrans₂ σ).app U) :
    strongTrans₂ τ = strongTrans₂ σ := sorry

/-- Restriction of an owner `2`-morphism commutes with the selected reindexing functors.

This is the objectwise selected-cleavage form of modification naturality. -/
@[reassoc]
theorem strongTrans₂.reindex (τ : F ⟶ G) {U V : C} (f : V ⟶ U)
    (x : X.p.Fiber U) :
    ((Functor.fiberPseudofunctor Y.p).map f.op.toLoc).toFunctor.map
        ((fiberNatTrans τ U).app x) =
      (Reindex.mapIso F f x).hom ≫
        (fiberNatTrans τ V).app ((Functor.Chosen.reindex X.p f).obj x) ≫
        (Reindex.mapIso G f x).inv := sorry

/-- The identity owner `2`-morphism induces the identity modification of its selected fiber
strong transformation. -/
@[simp]
theorem strongTrans₂.id (F : X ⟶ Y) :
    strongTrans₂ (𝟙 F) =
      Pseudofunctor.StrongTrans.Modification.id (strongTrans F) := sorry

/-- Passage from owner `2`-morphisms to selected-fiber modifications preserves vertical
composition. -/
@[simp]
theorem strongTrans₂.comp
    {H : X ⟶ Y} (τ : F ⟶ G) (σ : G ⟶ H) :
    strongTrans₂ (τ ≫ σ) =
      Pseudofunctor.StrongTrans.Modification.vcomp
        (strongTrans₂ τ) (strongTrans₂ σ) := sorry

end FiberedCategoryOver

end CategoryTheory
