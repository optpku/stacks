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
          (Functor.fiberPseudofunctor Y.p).map₂ η := sorry

/-- Identity coherence for the strong transformation induced by a morphism of fibred categories. -/
theorem strongTrans.naturality.id (F : X ⟶ Y) (a : LocallyDiscrete Cᵒᵖ) :
    (Cat.Hom.isoMk
          (Reindex.pseudonaturalityIso F ((𝟙 a : a ⟶ a).as.unop))).hom ≫
        (fiberFunctor F (unop a.as)).toCatHom ◁
          ((Functor.fiberPseudofunctor Y.p).mapId a).hom =
      ((Functor.fiberPseudofunctor X.p).mapId a).hom ▷
          (fiberFunctor F (unop a.as)).toCatHom ≫
        (λ_ ((fiberFunctor F (unop a.as)).toCatHom)).hom ≫
          (ρ_ ((fiberFunctor F (unop a.as)).toCatHom)).inv := sorry

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
            (α_ _ _ _).hom := sorry

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
    (strongTrans F).app U = (fiberFunctor F (unop U.as)).toCatHom := sorry

/-- The naturality isomorphism of `strongTrans F` is the Cat-bundled selected-cleavage
comparison. -/
@[simp]
theorem strongTrans.naturality (F : X ⟶ Y)
    {U V : LocallyDiscrete Cᵒᵖ} (f : U ⟶ V) :
    (strongTrans F).naturality f =
      Cat.Hom.isoMk (Reindex.pseudonaturalityIso F f.as.unop) := sorry

/-- The functor underlying the component of the induced strong transformation is the canonical
functor between the corresponding standard fibers. -/
@[simp]
theorem strongTrans.app.toFunctor (F : X ⟶ Y) (U : LocallyDiscrete Cᵒᵖ) :
    ((strongTrans F).app U).toFunctor =
      fiberFunctor F (unop U.as) := sorry

/-- The identity morphism of a fibred category induces the identity strong transformation of its
selected fiber pseudofunctor. -/
@[simp]
theorem strongTrans.id (X : FiberedCategoryOver.{u, v, uS, vS} C) :
    strongTrans (𝟙 X) =
      Pseudofunctor.StrongTrans.id
        (Functor.fiberPseudofunctor X.p) := sorry

/-- Passage from morphisms of fibred categories to selected-fiber strong transformations
preserves composition. -/
@[simp]
theorem strongTrans.comp
    {Z : FiberedCategoryOver.{u, v, uS, vS} C}
    (F : X ⟶ Y) (G : Y ⟶ Z) :
    strongTrans (F ≫ G) =
      Pseudofunctor.StrongTrans.vcomp
        (strongTrans F) (strongTrans G) := sorry

/-- Objectwise, the forward strong-transformation constraint is the inverse selected reindexing
comparison. -/
@[simp]
theorem strongTrans.naturality.hom.app (F : X ⟶ Y)
    {U V : LocallyDiscrete Cᵒᵖ} (f : U ⟶ V)
    (x : X.p.Fiber (unop U.as)) :
    ((strongTrans F).naturality f).hom.toNatTrans.app x =
      (Reindex.mapIso F f.as.unop x).inv := sorry

/-- Objectwise, the inverse strong-transformation constraint is the forward selected reindexing
comparison. -/
@[simp]
theorem strongTrans.naturality.inv.app (F : X ⟶ Y)
    {U V : LocallyDiscrete Cᵒᵖ} (f : U ⟶ V)
    (x : X.p.Fiber (unop U.as)) :
    ((strongTrans F).naturality f).inv.toNatTrans.app x =
      (Reindex.mapIso F f.as.unop x).hom := sorry

end FiberedCategoryOver

end CategoryTheory
