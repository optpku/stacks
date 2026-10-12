/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.Comparison.Map.Basic

/-!
# `2`-cell action of the relative-representability comparison map

This leaf sends a `2`-cell between morphisms into the canonical two-fibre product to the
corresponding natural transformation between ordinary categorical-pullback comparison functors,
and bundles the resulting local action as a functor on the hom category.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Bicategory
open CategoryTheory.Limits CategoryTheory.Limits.CategoricalPullback
open scoped CategoricalPullback
open scoped Pseudofunctor.StrongTrans

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Groupoids.PseudoPullbackComparison

section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-- A `2`-cell between maps into the canonical two-fibre product induces the corresponding
natural transformation between their ordinary categorical-pullback comparison maps. -/
@[stacks 0H2E "natural transformation between two-fibre-product comparison maps"]
noncomputable def map₂
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {A : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {M N : A ⟶ CategoryTheory.TwoFibreProduct.apex
      X.baseProjection X.baseProjection}
    (Γ : M ⟶ N) :
    map M ⟶ map N :=
  Functor.whiskerRight
    (Functor.whiskerRight Γ.hom.toNatTrans
      (BasedCategory.PseudoPullback.Comparison.functor
        (FiberedCategoryOver.Groupoids.toBasedFunctor X.baseProjection)
        (FiberedCategoryOver.Groupoids.toBasedFunctor X.baseProjection)))
    (FiberedCategoryOver.Groupoids.BaseProjection.pullbackDown X)

/-- The component of the induced comparison natural transformation is obtained by applying the
two deterministic pullback comparisons to the original `2`-cell component. -/
@[simp]
theorem map₂.app
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {A : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {M N : A ⟶ CategoryTheory.TwoFibreProduct.apex
      X.baseProjection X.baseProjection}
    (Γ : M ⟶ N) (a : A.total) :
    (map₂ Γ).app a =
      (FiberedCategoryOver.Groupoids.BaseProjection.pullbackDown X).map
        ((BasedCategory.PseudoPullback.Comparison.functor
          (FiberedCategoryOver.Groupoids.toBasedFunctor X.baseProjection)
          (FiberedCategoryOver.Groupoids.toBasedFunctor X.baseProjection)).map
          (Γ.hom.toNatTrans.app a)) := sorry

/-- The first projection of an induced comparison `2`-cell is the original component mapped by
the canonical first projection of the two-fibre product. -/
@[simp]
theorem map₂.app.fst
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {A : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {M N : A ⟶ CategoryTheory.TwoFibreProduct.apex
      X.baseProjection X.baseProjection}
    (Γ : M ⟶ N) (a : A.total) :
    ((map₂ Γ).app a).fst =
      (FiberedCategoryOver.Groupoids.toFunctor
        (CategoryTheory.TwoFibreProduct.cone
          X.baseProjection X.baseProjection).fst).map
        (Γ.hom.toNatTrans.app a) := sorry

/-- The second projection of an induced comparison `2`-cell is the original component mapped by
the canonical second projection of the two-fibre product. -/
@[simp]
theorem map₂.app.snd
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {A : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {M N : A ⟶ CategoryTheory.TwoFibreProduct.apex
      X.baseProjection X.baseProjection}
    (Γ : M ⟶ N) (a : A.total) :
    ((map₂ Γ).app a).snd =
      (FiberedCategoryOver.Groupoids.toFunctor
        (CategoryTheory.TwoFibreProduct.cone
          X.baseProjection X.baseProjection).snd).map
        (Γ.hom.toNatTrans.app a) := sorry

/-- The comparison-map `2`-cell is natural in morphisms of the source total category. -/
@[reassoc]
theorem map₂.naturality
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {A : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {M N : A ⟶ CategoryTheory.TwoFibreProduct.apex
      X.baseProjection X.baseProjection}
    (Γ : M ⟶ N) {a b : A.total} (f : a ⟶ b) :
    (map M).map f ≫ (map₂ Γ).app b =
      (map₂ Γ).app a ≫ (map N).map f := sorry

/-- The comparison-map `2`-cell action preserves identity cells. -/
@[simp]
theorem map₂.id
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {A : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    (M : A ⟶ CategoryTheory.TwoFibreProduct.apex
      X.baseProjection X.baseProjection) :
    map₂ (𝟙 M) = 𝟙 (map M) := sorry

/-- The comparison-map `2`-cell action preserves vertical composition. -/
@[simp]
theorem map₂.comp
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {A : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {M N P : A ⟶ CategoryTheory.TwoFibreProduct.apex
      X.baseProjection X.baseProjection}
    (Γ : M ⟶ N) (Δ : N ⟶ P) :
    map₂ (Γ ≫ Δ) = map₂ Γ ≫ map₂ Δ := sorry

/-- The comparison construction acts functorially on the hom category of morphisms into the
canonical two-fibre product. Its object and morphism data are the explicit `map` and `map₂`
constructions. -/
@[stacks 0H2E "local functor of two-fibre-product comparison maps"]
noncomputable def mapFunctor
    (X A : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C) :
    (A ⟶ CategoryTheory.TwoFibreProduct.apex
        X.baseProjection X.baseProjection) ⥤
      (A.total ⥤ X.p ⊡ X.p) where
  obj := map
  map := map₂
  map_id := map₂.id
  map_comp := map₂.comp

namespace mapFunctor

/-- The object action of the comparison-map hom functor is the canonical comparison functor. -/
@[simp]
theorem obj
    {X A : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    (M : A ⟶ CategoryTheory.TwoFibreProduct.apex
      X.baseProjection X.baseProjection) :
    (mapFunctor X A).obj M = map M := sorry

/-- The morphism action of the comparison-map hom functor is the canonical induced natural
transformation. -/
@[simp]
theorem map
    {X A : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {M N : A ⟶ CategoryTheory.TwoFibreProduct.apex
      X.baseProjection X.baseProjection} (Γ : M ⟶ N) :
    (mapFunctor X A).map Γ = map₂ Γ := sorry

end mapFunctor

/-- An invertible `2`-cell between morphisms into the canonical two-fibre product induces an
isomorphism between their comparison functors. -/
@[stacks 0H2E "isomorphism between two-fibre-product comparison maps"]
noncomputable def mapIso
    {X A : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {M N : A ⟶ CategoryTheory.TwoFibreProduct.apex
      X.baseProjection X.baseProjection} (e : M ≅ N) :
    map M ≅ map N :=
  (mapFunctor X A).mapIso e

namespace mapIso

/-- The forward natural transformation of an induced comparison isomorphism is the image of
the forward `2`-cell. -/
@[simp]
theorem hom
    {X A : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {M N : A ⟶ CategoryTheory.TwoFibreProduct.apex
      X.baseProjection X.baseProjection} (e : M ≅ N) :
    (mapIso e).hom = map₂ e.hom := sorry

/-- The inverse natural transformation of an induced comparison isomorphism is the image of
the inverse `2`-cell. -/
@[simp]
theorem inv
    {X A : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {M N : A ⟶ CategoryTheory.TwoFibreProduct.apex
      X.baseProjection X.baseProjection} (e : M ≅ N) :
    (mapIso e).inv = map₂ e.inv := sorry

end mapIso

end

end FiberedCategoryOver.Groupoids.PseudoPullbackComparison

end CategoryTheory
