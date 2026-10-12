/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Reindex
public import ReasLib.CategoryTheory.Fibered.Cleavage.Pseudofunctor.Construction
public import ReasLib.CategoryTheory.Sites.Descent.PullHom

/-!
# Reindexing comparisons on fiber Hom presheaves

This module contains the `pullHom` coherence of the canonical reindexing
comparison for a cartesian based functor with explicitly specified cleavages.
It is the application-facing expansion of
`Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor.mapHom_pullHom` for the
indexed fiber action: no new descent coherence is owned here.
-/

@[expose] public section

universe u v uS₁ vS₁ uS₂ vS₂

namespace CategoryTheory

open Opposite

namespace CartesianBasedFunctor

variable {C : Type u} [Category.{v} C]
variable {S₁ : Type uS₁} {S₂ : Type uS₂} [Category.{vS₁} S₁] [Category.{vS₂} S₂]
variable {p₁ : S₁ ⥤ C} {p₂ : S₂ ⥤ C}

set_option backward.isDefEq.respectTransparency false in
/-- Reindexing a comparison-conjugated fiber morphism commutes with `pullHom`.

This is the descent-facing coherence of `Reindex.mapIso` for explicit source and
target cleavages. -/
theorem Reindex.mapIso.pullHom.diagonal
    (F : CartesianBasedFunctor p₁ p₂) (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    {U V V' : C} (f : V ⟶ U) (g : V' ⟶ V) (gf : V' ⟶ U)
    (hgf : g ≫ f = gf) {x y : p₁.Fiber U}
    (d :
      (χ₁.toPseudofunctor.map f.op.toLoc).toFunctor.obj x ⟶
        (χ₁.toPseudofunctor.map f.op.toLoc).toFunctor.obj y) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := χ₂.toPseudofunctor)
        ((Reindex.mapIso F χ₁ χ₂ f x).hom ≫
          (F.fiberFunctor V).map d ≫
          (Reindex.mapIso F χ₁ χ₂ f y).inv)
        g gf gf hgf hgf =
      (Reindex.mapIso F χ₁ χ₂ gf x).hom ≫
        (F.fiberFunctor V').map
        (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
            (F := χ₁.toPseudofunctor) d g gf gf hgf hgf) ≫
        (Reindex.mapIso F χ₁ χ₂ gf y).inv := sorry

/-- Reindexing a comparison-conjugated two-leg fiber morphism commutes with `pullHom`.

The two displayed arrows `f₁` and `f₂` may have different targets.  This is the primary
descent-facing form because overlap morphisms naturally run between pullbacks along two legs of
one family; `Reindex.mapIso.pullHom.diagonal` is its diagonal specialization. Mathematically,
this is `IndexedFunctor.mapHom_pullHom` with both occurrences of `mapHom` expanded by
`Indexed.explicit.functor.mapHom`. -/
theorem Reindex.mapIso.pullHom.twoLeg
    (F : CartesianBasedFunctor p₁ p₂) (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    {U₁ U₂ V V' : C} (f₁ : V ⟶ U₁) (f₂ : V ⟶ U₂) (g : V' ⟶ V)
    (gf₁ : V' ⟶ U₁) (gf₂ : V' ⟶ U₂)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂)
    {x : p₁.Fiber U₁} {y : p₁.Fiber U₂}
    (d :
      (χ₁.toPseudofunctor.map f₁.op.toLoc).toFunctor.obj x ⟶
        (χ₁.toPseudofunctor.map f₂.op.toLoc).toFunctor.obj y) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := χ₂.toPseudofunctor)
        ((Reindex.mapIso F χ₁ χ₂ f₁ x).hom ≫
          (F.fiberFunctor V).map d ≫
          (Reindex.mapIso F χ₁ χ₂ f₂ y).inv)
        g gf₁ gf₂ hgf₁ hgf₂ =
      (Reindex.mapIso F χ₁ χ₂ gf₁ x).hom ≫
        (F.fiberFunctor V').map
          (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
            (F := χ₁.toPseudofunctor) d g gf₁ gf₂ hgf₁ hgf₂) ≫
        (Reindex.mapIso F χ₁ χ₂ gf₂ y).inv := sorry

/-- Literal-composite form of `Reindex.mapIso.pullHom.diagonal`.

This removes the factorization datum when the reindexed base arrow is written
as `g ≫ f`. -/
theorem Reindex.mapIso.pullHom.comp
    (F : CartesianBasedFunctor p₁ p₂) (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    {U V V' : C} (f : V ⟶ U) (g : V' ⟶ V) {x y : p₁.Fiber U}
    (d :
      (χ₁.toPseudofunctor.map f.op.toLoc).toFunctor.obj x ⟶
        (χ₁.toPseudofunctor.map f.op.toLoc).toFunctor.obj y) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := χ₂.toPseudofunctor)
        ((Reindex.mapIso F χ₁ χ₂ f x).hom ≫
          (F.fiberFunctor V).map d ≫
          (Reindex.mapIso F χ₁ χ₂ f y).inv)
        g (g ≫ f) (g ≫ f) =
      (Reindex.mapIso F χ₁ χ₂ (g ≫ f) x).hom ≫
        (F.fiberFunctor V').map
          (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
            (F := χ₁.toPseudofunctor) d g (g ≫ f) (g ≫ f)) ≫
        (Reindex.mapIso F χ₁ χ₂ (g ≫ f) y).inv := sorry

end CartesianBasedFunctor

end CategoryTheory
