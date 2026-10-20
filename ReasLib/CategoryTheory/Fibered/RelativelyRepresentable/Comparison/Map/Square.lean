/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.Comparison.Map.Basic

/-!
# Square of the relative-representability comparison map

This leaf packages a canonical comparison functor as a commutative square and exposes the
objectwise comparison isomorphisms identifying its two legs.
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

/-- The commutative square over X.p represented by a two-fibre-product comparison map. -/
@[stacks 0H2E "commutative square of the two-fibre-product comparison"]
noncomputable def map.square
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {A : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    (M : A ⟶ CategoryTheory.TwoFibreProduct.apex
      X.baseProjection X.baseProjection) :
    CatCommSqOver X.p X.p A.total :=
  (CategoricalPullback.toCatCommSqOver X.p X.p A.total).obj
    (map M)

/-- The objectwise comparison between the first leg of `map.square M` and the underlying left
owner composite. The comparison functors retain this component definitionally. -/
noncomputable def map.square.fstIso.app
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {A : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    (M : A ⟶ CategoryTheory.TwoFibreProduct.apex
      X.baseProjection X.baseProjection) (a : A.total) :
    ((map.square M).fst).obj a ≅
      (FiberedCategoryOver.Groupoids.toFunctor
        (M ≫ (CategoryTheory.TwoFibreProduct.cone
          X.baseProjection X.baseProjection).fst)).obj a :=
  Iso.refl _

/-- The explicit first-leg comparisons for `map.square M` are natural. -/
theorem map.square.fstIso.naturality
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {A : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    (M : A ⟶ CategoryTheory.TwoFibreProduct.apex
      X.baseProjection X.baseProjection)
    {a b : A.total} (f : a ⟶ b) :
    (map.square M).fst.map f ≫ (map.square.fstIso.app M b).hom =
      (map.square.fstIso.app M a).hom ≫
        (FiberedCategoryOver.Groupoids.toFunctor
          (M ≫ (CategoryTheory.TwoFibreProduct.cone
            X.baseProjection X.baseProjection).fst)).map f := sorry

/-- The first leg of `map.square M` is explicitly naturally isomorphic to the underlying left
owner composite. -/
@[stacks 0H2E "first-leg isomorphism of the two-fibre-product comparison map"]
noncomputable def map.square.fstIso
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {A : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    (M : A ⟶ CategoryTheory.TwoFibreProduct.apex
      X.baseProjection X.baseProjection) :
    (map.square M).fst ≅
      FiberedCategoryOver.Groupoids.toFunctor
        (M ≫ (CategoryTheory.TwoFibreProduct.cone
          X.baseProjection X.baseProjection).fst) :=
  NatIso.ofComponents
    (map.square.fstIso.app M)
    (fun f ↦ map.square.fstIso.naturality M f)

/-- The objectwise comparison between the second leg of `map.square M` and the underlying
right owner composite. The comparison functors retain this component definitionally. -/
noncomputable def map.square.sndIso.app
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {A : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    (M : A ⟶ CategoryTheory.TwoFibreProduct.apex
      X.baseProjection X.baseProjection) (a : A.total) :
    ((map.square M).snd).obj a ≅
      (FiberedCategoryOver.Groupoids.toFunctor
        (M ≫ (CategoryTheory.TwoFibreProduct.cone
          X.baseProjection X.baseProjection).snd)).obj a :=
  Iso.refl _

/-- The explicit second-leg comparisons for `map.square M` are natural. -/
theorem map.square.sndIso.naturality
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {A : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    (M : A ⟶ CategoryTheory.TwoFibreProduct.apex
      X.baseProjection X.baseProjection)
    {a b : A.total} (f : a ⟶ b) :
    (map.square M).snd.map f ≫ (map.square.sndIso.app M b).hom =
      (map.square.sndIso.app M a).hom ≫
        (FiberedCategoryOver.Groupoids.toFunctor
          (M ≫ (CategoryTheory.TwoFibreProduct.cone
            X.baseProjection X.baseProjection).snd)).map f := sorry

/-- The second leg of `map.square M` is explicitly naturally isomorphic to the underlying
right owner composite. -/
@[stacks 0H2E "second-leg isomorphism of the two-fibre-product comparison map"]
noncomputable def map.square.sndIso
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {A : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    (M : A ⟶ CategoryTheory.TwoFibreProduct.apex
      X.baseProjection X.baseProjection) :
    (map.square M).snd ≅
      FiberedCategoryOver.Groupoids.toFunctor
        (M ≫ (CategoryTheory.TwoFibreProduct.cone
          X.baseProjection X.baseProjection).snd) :=
  NatIso.ofComponents
    (map.square.sndIso.app M)
    (fun f ↦ map.square.sndIso.naturality M f)

/-- The forward component of the first-leg comparison for `map.square` is its explicit
objectwise identity comparison. -/
@[simp]
theorem map.square.fstIso.hom.app
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {A : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    (M : A ⟶ CategoryTheory.TwoFibreProduct.apex
      X.baseProjection X.baseProjection) (a : A.total) :
    (map.square.fstIso M).hom.app a = (map.square.fstIso.app M a).hom := sorry

/-- The inverse component of the first-leg comparison for `map.square` is its explicit
objectwise identity comparison. -/
@[simp]
theorem map.square.fstIso.inv.app
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {A : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    (M : A ⟶ CategoryTheory.TwoFibreProduct.apex
      X.baseProjection X.baseProjection) (a : A.total) :
    (map.square.fstIso M).inv.app a = (map.square.fstIso.app M a).inv := sorry

/-- The forward component of the second-leg comparison for `map.square` is its explicit
objectwise identity comparison. -/
@[simp]
theorem map.square.sndIso.hom.app
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {A : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    (M : A ⟶ CategoryTheory.TwoFibreProduct.apex
      X.baseProjection X.baseProjection) (a : A.total) :
    (map.square.sndIso M).hom.app a = (map.square.sndIso.app M a).hom := sorry

/-- The inverse component of the second-leg comparison for `map.square` is its explicit
objectwise identity comparison. -/
@[simp]
theorem map.square.sndIso.inv.app
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {A : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    (M : A ⟶ CategoryTheory.TwoFibreProduct.apex
      X.baseProjection X.baseProjection) (a : A.total) :
    (map.square.sndIso M).inv.app a = (map.square.sndIso.app M a).inv := sorry

end

end FiberedCategoryOver.Groupoids.PseudoPullbackComparison

end CategoryTheory
