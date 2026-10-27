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
      π₁ (toFunctor X.baseProjection) (toFunctor X.baseProjection) := rfl

/-- pullbackDown preserves the second projection.

Proof strategy: unfold pullbackDown, CategoricalPullback.postcompose, and
CategoricalPullback.LegChange.map; both component
functors retain the second object and morphism fields, so functor extensionality closes the goal. -/
@[simp] theorem pullbackDown_snd
    (X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C) :
    pullbackDown X ⋙ π₂ X.p X.p =
      π₂ (toFunctor X.baseProjection) (toFunctor X.baseProjection) := rfl

/-- On objects, `pullbackDown` retains the first component of the categorical pullback. -/
@[simp] theorem pullbackDown_obj_fst
    (X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C)
    (x : (toFunctor X.baseProjection) ⊡ (toFunctor X.baseProjection)) :
    ((pullbackDown X).obj x).fst = x.fst := rfl
/- Proof strategy: evaluate `pullbackDown_fst X` at `x` and read the object component. -/

/-- On objects, `pullbackDown` retains the second component of the categorical pullback. -/
@[simp] theorem pullbackDown_obj_snd
    (X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C)
    (x : (toFunctor X.baseProjection) ⊡ (toFunctor X.baseProjection)) :
    ((pullbackDown X).obj x).snd = x.snd := rfl
/- Proof strategy: evaluate `pullbackDown_snd X` at `x` and read the object component. -/

/-- On objects, `pullbackDown` maps the structural isomorphism through the canonical base
projection and conjugates it by the two source-facing projection comparisons. -/
@[simp] theorem pullbackDown_obj_iso
    (X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C)
    (x : (toFunctor X.baseProjection) ⊡ (toFunctor X.baseProjection)) :
    ((pullbackDown X).obj x).iso =
      ((baseProjection.iso X).app x.fst).symm ≪≫
        (base C).p.mapIso x.iso ≪≫
          (baseProjection.iso X).app x.snd := by
  have h :
      ((CategoricalPullback.postcompose
        (toFunctor X.baseProjection) (toFunctor X.baseProjection) (base C).p).obj x).iso =
        (base C).p.mapIso x.iso := by
    apply Iso.ext
    change 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫ (base C).p.map x.iso.hom ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ =
      (base C).p.map x.iso.hom
    simp only [Category.id_comp, Category.comp_id]
  apply Iso.ext
  change 𝟙 _ ≫ ((𝟙 _ ≫ (baseProjection.iso.{u, v, w, w} X).inv.app x.fst) ≫ 𝟙 _) ≫
      𝟙 _ ≫ ((CategoricalPullback.postcompose
        (toFunctor X.baseProjection) (toFunctor X.baseProjection) (base C).p).obj x).iso.hom ≫
      𝟙 _ ≫ (𝟙 _ ≫ (baseProjection.iso.{u, v, w, w} X).hom.app x.snd ≫ 𝟙 _) ≫ 𝟙 _ = _
  rw [h]
  simp only [Functor.mapIso_hom, Category.id_comp, Category.comp_id]
  rfl
/- Both structural-map formulas are computed directly from the explicit cospan maps. -/

/-- The forward map of the structural isomorphism carried by `pullbackDown.obj x` is the
corresponding three-step conjugation. -/
@[simp] theorem pullbackDown_obj_iso_hom
    (X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C)
    (x : (toFunctor X.baseProjection) ⊡ (toFunctor X.baseProjection)) :
    ((pullbackDown X).obj x).iso.hom =
      (baseProjection.iso X).inv.app x.fst ≫
        (base C).p.map x.iso.hom ≫
          (baseProjection.iso X).hom.app x.snd := by
  rw [pullbackDown_obj_iso.{w, v, u, w, w}]
  rfl

/-- The inverse map of the structural isomorphism carried by `pullbackDown.obj x` is the
reverse three-step conjugation. -/
@[simp] theorem pullbackDown_obj_iso_inv
    (X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C)
    (x : (toFunctor X.baseProjection) ⊡ (toFunctor X.baseProjection)) :
    ((pullbackDown X).obj x).iso.inv =
      (baseProjection.iso X).inv.app x.snd ≫
        (base C).p.map x.iso.inv ≫
          (baseProjection.iso X).hom.app x.fst := by
  rw [pullbackDown_obj_iso.{w, v, u, w, w}]
  simp only [Iso.trans_inv, Iso.symm_inv, Iso.app_inv, Functor.mapIso_inv, Category.assoc]
  rfl

/-- On morphisms, `pullbackDown` retains the first component map. -/
@[simp] theorem pullbackDown_map_fst
    (X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C)
    {x y : (toFunctor X.baseProjection) ⊡ (toFunctor X.baseProjection)} (f : x ⟶ y) :
    ((pullbackDown X).map f).fst = f.fst := rfl
/- Proof strategy: evaluate `pullbackDown_fst X` on `f` and read the map component. -/

/-- On morphisms, `pullbackDown` retains the second component map. -/
@[simp] theorem pullbackDown_map_snd
    (X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C)
    {x y : (toFunctor X.baseProjection) ⊡ (toFunctor X.baseProjection)} (f : x ⟶ y) :
    ((pullbackDown X).map f).snd = f.snd := rfl
/- Proof strategy: evaluate `pullbackDown_snd X` on `f` and read the map component. -/

/-- Forgetting the universe-resized identity-fibration base induces an equivalence of
self-pullbacks. -/
instance pullbackDown.isEquivalence
    (X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C) :
    (pullbackDown X).IsEquivalence := by
  let up : X.p ⊡ X.p ⥤ (toFunctor X.baseProjection) ⊡ (toFunctor X.baseProjection) :=
    CategoricalPullback.postcompose X.p X.p (baseSection.{u, v, w} C)
  have down_hom (x : (toFunctor X.baseProjection) ⊡ (toFunctor X.baseProjection)) :
      ((pullbackDown X).obj x).iso.hom = (base C).p.map x.iso.hom := by
    rw [pullbackDown_obj_iso_hom.{w, v, u, w, w}]
    change ((𝟙 _ ≫ 𝟙 _) ≫ 𝟙 _) ≫ (base C).p.map x.iso.hom ≫ (𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _) = _
    simp only [Category.id_comp, Category.comp_id]
  let unit : 𝟭 _ ≅ pullbackDown X ⋙ up :=
    NatIso.ofComponents
      (fun x => CategoricalPullback.mkIso (Iso.refl _) (Iso.refl _) (by
        change (toFunctor X.baseProjection).map (𝟙 x.fst) ≫ (up.obj ((pullbackDown X).obj x)).iso.hom =
          x.iso.hom ≫ (toFunctor X.baseProjection).map (𝟙 x.snd)
        rw [Functor.map_id, Functor.map_id]
        change 𝟙 _ ≫ (𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫
            (baseSection.{u, v, w} C).map (((pullbackDown X).obj x).iso.hom) ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _) =
          x.iso.hom ≫ 𝟙 _
        rw [down_hom]
        change 𝟙 _ ≫ (𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫ x.iso.hom ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _) =
          x.iso.hom ≫ 𝟙 _
        simp only [Category.id_comp, Category.comp_id]))
      (by
        intro x y f
        apply CategoricalPullback.hom_ext
        · change f.fst ≫ 𝟙 _ = 𝟙 _ ≫ f.fst
          simp only [Category.id_comp, Category.comp_id]
        · change f.snd ≫ 𝟙 _ = 𝟙 _ ≫ f.snd
          simp only [Category.id_comp, Category.comp_id])
  let counit : up ⋙ pullbackDown X ≅ 𝟭 _ :=
    NatIso.ofComponents
      (fun x => CategoricalPullback.mkIso (Iso.refl _) (Iso.refl _) (by
        change X.p.map (𝟙 x.fst) ≫ x.iso.hom =
          ((pullbackDown X).obj (up.obj x)).iso.hom ≫ X.p.map (𝟙 x.snd)
        rw [down_hom]
        change X.p.map (𝟙 x.fst) ≫ x.iso.hom =
          (𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫ x.iso.hom ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _) ≫ X.p.map (𝟙 x.snd)
        simp only [Functor.map_id, Category.id_comp, Category.comp_id]))
      (by
        intro x y f
        apply CategoricalPullback.hom_ext
        · change f.fst ≫ 𝟙 _ = 𝟙 _ ≫ f.fst
          simp only [Category.id_comp, Category.comp_id]
        · change f.snd ≫ 𝟙 _ = 𝟙 _ ≫ f.snd
          simp only [Category.id_comp, Category.comp_id])
  exact Functor.IsEquivalence.mk' up unit counit
/- The inverse postcomposes the structural isomorphism with the explicit `baseSection`.
Both composites have identity components on the two legs; the structural-map calculations
above prove their compatibility without using the deferred base-change property instances. -/

end BaseProjection
end FiberedCategoryOver.Groupoids

end CategoryTheory
