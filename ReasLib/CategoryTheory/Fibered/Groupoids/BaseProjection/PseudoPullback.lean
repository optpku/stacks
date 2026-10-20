/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

-- Import decisions:
-- * `CategoricalPullback.Diagonal.Basic` owns common-base postcomposition.
-- * `CategoricalPullback.Equivalences.Legs` owns transport along the two leg isomorphisms.
-- * `Groupoids.Base` owns the universe-closed identity fibration and its canonical
--   base projection.
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Diagonal.Basic
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Equivalences.Legs
public import ReasLib.CategoryTheory.Fibered.Groupoids.Base

/-!
# Base-projection pseudo-pullback comparison

This leaf removes the universe-closed identity-fibration base from the self-pullback of a
groupoid-fibred category. It is independent of relative representability and of any
pseudo-pullback cone comparison that later uses it.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open CategoryTheory.Limits CategoryTheory.Limits.CategoricalPullback
open scoped CategoricalPullback

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Groupoids
namespace BaseProjection

/- Notation decision: no notation is introduced. The direction encoded by pullbackDown is
important at its use sites and should remain visible. -/

/-- Forget the closed identity-fibration owner in the self-pullback of the canonical base
projection.

The construction has the source-facing direction

```
(X.p ⋙ baseSection) ⊡ (X.p ⋙ baseSection) ───── pullbackDown X ─────▶ X.p ⊡ X.p
```

It maps the structural isomorphism through the bundled projection `(base C).p` and then transports
both legs along `baseProjection.iso X`. Thus the non-Prop functor data are explicit and do not
depend on a chosen quasi-inverse of a pullback equivalence or expose the implementation `ULift`. -/
noncomputable def pullbackDown
    (X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C) :
    (toFunctor X.baseProjection) ⊡ (toFunctor X.baseProjection) ⥤ X.p ⊡ X.p :=
  CategoricalPullback.postcompose
      (toFunctor X.baseProjection) (toFunctor X.baseProjection)
      (base C).p ⋙
    CategoricalPullback.LegChange.map
      (baseProjection.iso X)
      (baseProjection.iso X)

/-- pullbackDown preserves the first projection.

Proof strategy: unfold pullbackDown, CategoricalPullback.postcompose, and
CategoricalPullback.LegChange.map; both component
functors retain the first object and morphism fields, so functor extensionality closes the goal. -/
@[simp] theorem pullbackDown_fst
    (X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C) :
    pullbackDown X ⋙ π₁ X.p X.p =
      π₁ (toFunctor X.baseProjection) (toFunctor X.baseProjection) := sorry

/-- pullbackDown preserves the second projection.

Proof strategy: unfold pullbackDown, CategoricalPullback.postcompose, and
CategoricalPullback.LegChange.map; both component
functors retain the second object and morphism fields, so functor extensionality closes the goal. -/
@[simp] theorem pullbackDown_snd
    (X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C) :
    pullbackDown X ⋙ π₂ X.p X.p =
      π₂ (toFunctor X.baseProjection) (toFunctor X.baseProjection) := sorry

/-- On objects, `pullbackDown` retains the first component of the categorical pullback. -/
@[simp] theorem pullbackDown_obj_fst
    (X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C)
    (x : (toFunctor X.baseProjection) ⊡ (toFunctor X.baseProjection)) :
    ((pullbackDown X).obj x).fst = x.fst := sorry
/- Proof strategy: evaluate `pullbackDown_fst X` at `x` and read the object component. -/

/-- On objects, `pullbackDown` retains the second component of the categorical pullback. -/
@[simp] theorem pullbackDown_obj_snd
    (X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C)
    (x : (toFunctor X.baseProjection) ⊡ (toFunctor X.baseProjection)) :
    ((pullbackDown X).obj x).snd = x.snd := sorry
/- Proof strategy: evaluate `pullbackDown_snd X` at `x` and read the object component. -/

/-- On objects, `pullbackDown` maps the structural isomorphism through the canonical base
projection and conjugates it by the two source-facing projection comparisons. -/
@[simp] theorem pullbackDown_obj_iso
    (X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C)
    (x : (toFunctor X.baseProjection) ⊡ (toFunctor X.baseProjection)) :
    ((pullbackDown X).obj x).iso =
      ((baseProjection.iso X).app x.fst).symm ≪≫
        (base C).p.mapIso x.iso ≪≫
          (baseProjection.iso X).app x.snd := sorry
/- Proof strategy: combine `CategoricalPullback.postcompose.obj.iso.hom` and
`CategoricalPullback.postcompose.obj.iso.inv` with `CategoricalPullback.LegChange.map.obj.iso`. -/

/-- The forward map of the structural isomorphism carried by `pullbackDown.obj x` is the
corresponding three-step conjugation. -/
@[simp] theorem pullbackDown_obj_iso_hom
    (X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C)
    (x : (toFunctor X.baseProjection) ⊡ (toFunctor X.baseProjection)) :
    ((pullbackDown X).obj x).iso.hom =
      (baseProjection.iso X).inv.app x.fst ≫
        (base C).p.map x.iso.hom ≫
          (baseProjection.iso X).hom.app x.snd := sorry

/-- The inverse map of the structural isomorphism carried by `pullbackDown.obj x` is the
reverse three-step conjugation. -/
@[simp] theorem pullbackDown_obj_iso_inv
    (X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C)
    (x : (toFunctor X.baseProjection) ⊡ (toFunctor X.baseProjection)) :
    ((pullbackDown X).obj x).iso.inv =
      (baseProjection.iso X).inv.app x.snd ≫
        (base C).p.map x.iso.inv ≫
          (baseProjection.iso X).hom.app x.fst := sorry

/-- On morphisms, `pullbackDown` retains the first component map. -/
@[simp] theorem pullbackDown_map_fst
    (X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C)
    {x y : (toFunctor X.baseProjection) ⊡ (toFunctor X.baseProjection)} (f : x ⟶ y) :
    ((pullbackDown X).map f).fst = f.fst := sorry
/- Proof strategy: evaluate `pullbackDown_fst X` on `f` and read the map component. -/

/-- On morphisms, `pullbackDown` retains the second component map. -/
@[simp] theorem pullbackDown_map_snd
    (X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C)
    {x y : (toFunctor X.baseProjection) ⊡ (toFunctor X.baseProjection)} (f : x ⟶ y) :
    ((pullbackDown X).map f).snd = f.snd := sorry
/- Proof strategy: evaluate `pullbackDown_snd X` on `f` and read the map component. -/

/-- Forgetting the universe-resized identity-fibration base induces an equivalence of
self-pullbacks. -/
instance pullbackDown.isEquivalence
    (X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C) :
    (pullbackDown X).IsEquivalence := sorry
/- Proof strategy: factor `pullbackDown` into base change along `(base C).p`, the inverse
functor of mathlib's canonical `ULift.equivalence`, and congruence along
`baseProjection.iso`; both factors are equivalences. -/

end BaseProjection
end FiberedCategoryOver.Groupoids

end CategoryTheory
