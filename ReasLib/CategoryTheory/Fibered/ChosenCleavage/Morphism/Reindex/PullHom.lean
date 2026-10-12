/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Reindex.PullHom
public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Morphism.Reindex

/-!
# Pullback coherence for selected reindexing comparisons

This module specializes the explicit-cleavage `pullHom` coherence of a
cartesian based functor to the standard selected cleavages of fibred
categories.
-/

@[expose] public section

universe u v uS vS

namespace CategoryTheory

open Opposite

namespace FiberedCategoryOver

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.{u, v, uS, vS} C}

/-- Pulling back a selected reindexing-comparison conjugate is the corresponding conjugate of
the pulled-back source fiber morphism.

This is the selected-cleavage specialization of
`CartesianBasedFunctor.Reindex.mapIso.pullHom.diagonal`. -/
theorem Reindex.mapIso.pullHom.diagonal
    (F : X ⟶ Y) {U V V' : C} (f : V ⟶ U) (g : V' ⟶ V) (gf : V' ⟶ U)
    (hgf : g ≫ f = gf) {x y : X.p.Fiber U}
    (d :
      ((Functor.fiberPseudofunctor X.p).map f.op.toLoc).toFunctor.obj x ⟶
        ((Functor.fiberPseudofunctor X.p).map f.op.toLoc).toFunctor.obj y) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := Functor.fiberPseudofunctor Y.p)
        ((Reindex.mapIso F f x).hom ≫
          (fiberFunctor F V).map d ≫
          (Reindex.mapIso F f y).inv)
        g gf gf hgf hgf =
      (Reindex.mapIso F gf x).hom ≫
        (fiberFunctor F V').map
          (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
            (F := Functor.fiberPseudofunctor X.p) d g gf gf hgf hgf) ≫
        (Reindex.mapIso F gf y).inv := sorry

/-- Pulling back a selected reindexing-comparison conjugate along two distinct legs is the
corresponding conjugate of the pulled-back source fiber morphism.

This is the selected-cleavage specialization of
`CartesianBasedFunctor.Reindex.mapIso.pullHom.twoLeg`. -/
theorem Reindex.mapIso.pullHom.twoLeg
    (F : X ⟶ Y) {U₁ U₂ V V' : C}
    (f₁ : V ⟶ U₁) (f₂ : V ⟶ U₂) (g : V' ⟶ V)
    (gf₁ : V' ⟶ U₁) (gf₂ : V' ⟶ U₂)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂)
    {x : X.p.Fiber U₁} {y : X.p.Fiber U₂}
    (d :
      ((Functor.fiberPseudofunctor X.p).map f₁.op.toLoc).toFunctor.obj x ⟶
        ((Functor.fiberPseudofunctor X.p).map f₂.op.toLoc).toFunctor.obj y) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := Functor.fiberPseudofunctor Y.p)
        ((Reindex.mapIso F f₁ x).hom ≫
          (fiberFunctor F V).map d ≫
          (Reindex.mapIso F f₂ y).inv)
        g gf₁ gf₂ hgf₁ hgf₂ =
      (Reindex.mapIso F gf₁ x).hom ≫
        (fiberFunctor F V').map
          (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
            (F := Functor.fiberPseudofunctor X.p) d g gf₁ gf₂ hgf₁ hgf₂) ≫
        (Reindex.mapIso F gf₂ y).inv := sorry

end FiberedCategoryOver

end CategoryTheory
