/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.IndexedFunctor.Chosen
public import ReasLib.CategoryTheory.Fibered.CategoryOver.Fiber
public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Morphism.Naturality
public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Morphism.Reindex

/-!
# Direct indexed fiber action of fibred-category morphisms

This module specializes the selected-cleavage cartesian based functor action to
the bicategory `FiberedCategoryOver C`, with computation rules for the direct
object and composition actions.
-/

@[expose] public section

universe uC vC uS vS

namespace CategoryTheory

open Functor Opposite
open scoped CategoryTheory.Bicategory

namespace FiberedCategoryOver

variable {C : Type uC} [Category.{vC} C]
variable {X : FiberedCategoryOver.{uC, vC, uS, vS} C}
variable {Y : FiberedCategoryOver.{uC, vC, uS, vS} C}

/-- A morphism of fibred categories over a common base, viewed directly as an indexed functor
between the selected fiber pseudofunctors.  The cleavage-explicit owner is
`CartesianBasedFunctor.Indexed.explicit.functor`. -/
noncomputable def Indexed.functor (F : X ⟶ Y) :
    Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor (𝟭 C)
      (Functor.fiberPseudofunctor X.p) (Functor.fiberPseudofunctor Y.p) :=
  CartesianBasedFunctor.Indexed.chosen.functor (toCartesianBasedFunctor F)

/-- Components of the indexed functor associated to a fibred-category morphism are its ordinary
fiber functors. -/
@[simp]
theorem Indexed.functor.app (F : X ⟶ Y) (U : C) :
    (Indexed.functor F).app U = fiberFunctor F U := sorry

/-- Naturality of the indexed functor associated to a fibred-category morphism is the selected
reindexing comparison in inverse orientation. -/
@[simp]
theorem Indexed.functor.naturality (F : X ⟶ Y)
    {U V : C} (f : V ⟶ U) :
    (Indexed.functor F).naturality f =
      Reindex.pseudonaturalityIso F f := sorry

/-- Forward naturality components of the indexed functor associated to a fibred-category
morphism are inverse selected reindexing comparisons. -/
@[simp]
theorem Indexed.functor.naturality.hom.app (F : X ⟶ Y)
    {U V : C} (f : V ⟶ U) (x : X.p.Fiber U) :
    ((Indexed.functor F).naturality f).hom.app x =
      (Reindex.mapIso F f x).inv := sorry

/-- Inverse naturality components of the indexed functor associated to a fibred-category
morphism are forward selected reindexing comparisons. -/
@[simp]
theorem Indexed.functor.naturality.inv.app (F : X ⟶ Y)
    {U V : C} (f : V ⟶ U) (x : X.p.Fiber U) :
    ((Indexed.functor F).naturality f).inv.app x =
      (Reindex.mapIso F f x).hom := sorry

/-- Restricted-morphism transport for a fibred-category morphism is inherited from the canonical
selected-cleavage indexed functor. -/
@[simp]
theorem Indexed.functor.mapHom (F : X ⟶ Y)
    {U₁ U₂ V : C} (f₁ : V ⟶ U₁) (f₂ : V ⟶ U₂)
    {x : X.p.Fiber U₁} {y : X.p.Fiber U₂}
    (φ :
      ((Functor.fiberPseudofunctor X.p).map
        f₁.op.toLoc).toFunctor.obj x ⟶
      ((Functor.fiberPseudofunctor X.p).map
        f₂.op.toLoc).toFunctor.obj y) :
    (Indexed.functor F).mapHom f₁ f₂ φ =
      (Reindex.mapIso F f₁ x).hom ≫
        (fiberFunctor F V).map φ ≫
      (Reindex.mapIso F f₂ y).inv := sorry

/-- Total-category readout of restricted-morphism transport for a fibred-category morphism. -/
theorem Indexed.functor.mapHom.toTotal (F : X ⟶ Y)
    {U₁ U₂ V : C} (f₁ : V ⟶ U₁) (f₂ : V ⟶ U₂)
    {x : X.p.Fiber U₁} {y : X.p.Fiber U₂}
    (φ :
      ((Functor.fiberPseudofunctor X.p).map
        f₁.op.toLoc).toFunctor.obj x ⟶
      ((Functor.fiberPseudofunctor X.p).map
        f₂.op.toLoc).toFunctor.obj y) :
    ((Indexed.functor F).mapHom f₁ f₂ φ).1 =
      (Reindex.mapIso F f₁ x).hom.1 ≫
        ((fiberFunctor F V).map φ).1 ≫
      (Reindex.mapIso F f₂ y).inv.1 := sorry

/-- The direct indexed fiber action of the identity fibred-category morphism is the identity
indexed functor. -/
@[simp]
theorem Indexed.functor.id
    (X : FiberedCategoryOver.{uC, vC, uS, vS} C) :
    Indexed.functor (𝟙 X) =
      Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor.id
        (Functor.fiberPseudofunctor X.p) := sorry

/-- The direct indexed fiber action of a composite fibred-category morphism is the composite
of the indexed fiber actions of its factors. -/
@[simp]
theorem Indexed.functor.comp
    {Z : FiberedCategoryOver.{uC, vC, uS, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) :
    Indexed.functor (F ≫ G) =
      (Indexed.functor F).comp (Indexed.functor G) := sorry

end FiberedCategoryOver

end CategoryTheory
