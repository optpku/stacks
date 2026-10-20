/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute

-- Import decisions:
-- * `BaseProjection` owns the deterministic transport out of the universe-closed base.
-- * `PseudoPullback.Cone` owns pseudo-pullback cones and their leg data.
-- * `UnderlyingFunctorIso` owns the passage from a 2-cell of fibred categories to a natural
--   isomorphism of total functors.
public import ReasLib.CategoryTheory.Fibered.Groupoids.BaseProjection.PseudoPullback
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Fibered.Groupoids.UnderlyingFunctorIso

/-!
# Basic cone target comparison for relative representability

This leaf turns a pseudo-pullback cone over the canonical base projection into the ordinary
self-pullback functor of its two total legs.  It owns the resulting functor and its object and morphism computations.
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

/-- The categorical-pullback functor determined by a pseudo-pullback cone over baseProjection,
with its ULift-valued comparison transported back to the ordinary self-pullback of X.p. -/
@[stacks 0H2E "categorical-pullback target of a pseudo-pullback cone"]
noncomputable def target
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    (P : Bicategory.PseudoPullbackCone X.baseProjection X.baseProjection) :
    P.pt.total ⥤ X.p ⊡ X.p :=
  (CategoricalPullback.functorEquiv
    (FiberedCategoryOver.Groupoids.toFunctor X.baseProjection)
    (FiberedCategoryOver.Groupoids.toFunctor X.baseProjection) P.pt.total).inverse.obj
      { fst := FiberedCategoryOver.Groupoids.toFunctor P.fst
        snd := FiberedCategoryOver.Groupoids.toFunctor P.snd
        iso := FiberedCategoryOver.Groupoids.toFunctorIso P.iso } ⋙
    FiberedCategoryOver.Groupoids.BaseProjection.pullbackDown X

/-- The left projection of `target P` is the underlying left leg of `P`.

Proof strategy: use BaseProjection.pullbackDown_fst and the left projection of
CategoricalPullback.functorEquiv.inverse. -/
@[simp] theorem target.fst
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    (P : Bicategory.PseudoPullbackCone X.baseProjection X.baseProjection) :
    target P ⋙ π₁ X.p X.p =
      FiberedCategoryOver.Groupoids.toFunctor P.fst := sorry

/-- The right projection of `target P` is the underlying right leg of `P`.

Proof strategy: use BaseProjection.pullbackDown_snd and the right projection of
CategoricalPullback.functorEquiv.inverse. -/
@[simp] theorem target.snd
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    (P : Bicategory.PseudoPullbackCone X.baseProjection X.baseProjection) :
    target P ⋙ π₂ X.p X.p =
      FiberedCategoryOver.Groupoids.toFunctor P.snd := sorry

/-- Objectwise, the first projection of `target P` is the underlying left leg of `P`. -/
@[simp] theorem target.obj.fst
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    (P : Bicategory.PseudoPullbackCone X.baseProjection X.baseProjection) (a : P.pt.total) :
    ((target P).obj a).fst =
      (FiberedCategoryOver.Groupoids.toFunctor P.fst).obj a := sorry
/- Proof strategy: evaluate `target.fst P` at `a` and read the object component. -/

/-- Objectwise, the second projection of `target P` is the underlying right leg of `P`. -/
@[simp] theorem target.obj.snd
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    (P : Bicategory.PseudoPullbackCone X.baseProjection X.baseProjection) (a : P.pt.total) :
    ((target P).obj a).snd =
      (FiberedCategoryOver.Groupoids.toFunctor P.snd).obj a := sorry
/- Proof strategy: evaluate `target.snd P` at `a` and read the object component. -/

/-- Objectwise, the structural isomorphism of `target P` is the cone comparison transported
from the universe-closed identity fibration back to the original base `C`. -/
@[simp] theorem target.obj.iso
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    (P : Bicategory.PseudoPullbackCone X.baseProjection X.baseProjection)
    (a : P.pt.total) :
    ((target P).obj a).iso =
      ((FiberedCategoryOver.Groupoids.baseProjection.iso X).app
        ((FiberedCategoryOver.Groupoids.toFunctor P.fst).obj a)).symm ≪≫
        (FiberedCategoryOver.Groupoids.base C).p.mapIso
          ((FiberedCategoryOver.Groupoids.toFunctorIso P.iso).app a) ≪≫
          (FiberedCategoryOver.Groupoids.baseProjection.iso X).app
            ((FiberedCategoryOver.Groupoids.toFunctor P.snd).obj a) := sorry
/- Proof strategy: use the generated object formula for
`CategoricalPullback.functorEquiv.inverse`, followed by
`BaseProjection.pullbackDown_obj_iso`. -/

/-- The forward map of the structural isomorphism carried by `target P` is the underlying
cone comparison mapped to `C` and conjugated by the two base-projection comparisons. -/
@[simp] theorem target.obj.iso.hom
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    (P : Bicategory.PseudoPullbackCone X.baseProjection X.baseProjection)
    (a : P.pt.total) :
    ((target P).obj a).iso.hom =
      (FiberedCategoryOver.Groupoids.baseProjection.iso X).inv.app
          ((FiberedCategoryOver.Groupoids.toFunctor P.fst).obj a) ≫
        (FiberedCategoryOver.Groupoids.base C).p.map
          ((FiberedCategoryOver.Groupoids.toFunctorIso P.iso).hom.app a) ≫
          (FiberedCategoryOver.Groupoids.baseProjection.iso X).hom.app
            ((FiberedCategoryOver.Groupoids.toFunctor P.snd).obj a) := sorry

/-- The inverse map of the structural isomorphism carried by `target P` is the reverse
conjugation of the inverse underlying cone comparison. -/
@[simp] theorem target.obj.iso.inv
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    (P : Bicategory.PseudoPullbackCone X.baseProjection X.baseProjection)
    (a : P.pt.total) :
    ((target P).obj a).iso.inv =
      (FiberedCategoryOver.Groupoids.baseProjection.iso X).inv.app
          ((FiberedCategoryOver.Groupoids.toFunctor P.snd).obj a) ≫
        (FiberedCategoryOver.Groupoids.base C).p.map
          ((FiberedCategoryOver.Groupoids.toFunctorIso P.iso).inv.app a) ≫
          (FiberedCategoryOver.Groupoids.baseProjection.iso X).hom.app
            ((FiberedCategoryOver.Groupoids.toFunctor P.fst).obj a) := sorry

/-- On morphisms, the first projection of `target P` is the map of the underlying left leg. -/
@[simp] theorem target.hom.fst
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    (P : Bicategory.PseudoPullbackCone X.baseProjection X.baseProjection)
    {a b : P.pt.total} (f : a ⟶ b) :
    ((target P).map f).fst =
      (FiberedCategoryOver.Groupoids.toFunctor P.fst).map f := sorry
/- Proof strategy: evaluate `target.fst P` on `f` and read the morphism component. -/

/-- On morphisms, the second projection of `target P` is the map of the underlying right leg. -/
@[simp] theorem target.hom.snd
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    (P : Bicategory.PseudoPullbackCone X.baseProjection X.baseProjection)
    {a b : P.pt.total} (f : a ⟶ b) :
    ((target P).map f).snd =
      (FiberedCategoryOver.Groupoids.toFunctor P.snd).map f := sorry
/- Proof strategy: evaluate `target.snd P` on `f` and read the morphism component. -/

end

end FiberedCategoryOver.Groupoids.PseudoPullbackComparison

end CategoryTheory
