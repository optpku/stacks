/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute

-- Import decisions:
-- * `BaseProjection` owns the deterministic transport from the universe-closed base back to `C`.
-- * `PseudoPullback.Comparison.Functor` owns the deterministic comparison from the bicategorical
--   pseudo-pullback to an ordinary categorical pullback.
-- * `BasedCategory.InGroupoids.PseudoPullback` owns the closure instance required by the
--   property-selected groupoid-fibred two-fibre-product apex.
-- * `TwoFibreProduct.FullSubbicategory.Bilimit` owns the canonical apex and cone used by `map`.
public import ReasLib.CategoryTheory.Fibered.Groupoids.BaseProjection.PseudoPullback
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Comparison.Functor
public import ReasLib.CategoryTheory.Fibered.BasedCategory.InGroupoids.PseudoPullback
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Bilimit

/-!
# Basic map comparison for relative representability

This leaf turns a morphism into the canonical two-fibre product into a functor to the ordinary
self-pullback of the underlying fibration.  It owns the resulting functor and its explicit object and morphism computations.
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

/- The owner morphisms below live in a dependent sub-2-category. Their common total-object
universe is the universe-closed level max w (max u v) of the canonical pseudo-pullback. The
ordinary comparison target nevertheless lives over X.p: the explicit BaseProjection.pullbackDown
bridge removes the implementation-level ULift C from the mathematical API. -/
section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-- A morphism into the canonical two-fibre product, viewed in the ordinary self-pullback of X.p.

The first two factors pass from the bicategorical owner to the categorical pullback over ULift C;
BaseProjection.pullbackDown then returns to the source-facing pullback over C. -/
@[stacks 0H2E "comparison map from a two-fibre-product cone"]
noncomputable def map
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {A : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
  (M : A ⟶ CategoryTheory.TwoFibreProduct.apex
      X.baseProjection X.baseProjection) :
    A.total ⥤ X.p ⊡ X.p :=
  FiberedCategoryOver.Groupoids.toFunctor M ⋙
    BasedCategory.PseudoPullback.Comparison.functor
      (FiberedCategoryOver.Groupoids.toBasedFunctor X.baseProjection)
      (FiberedCategoryOver.Groupoids.toBasedFunctor X.baseProjection) ⋙
    FiberedCategoryOver.Groupoids.BaseProjection.pullbackDown X

/-- The intermediate categorical-pullback object used to form `(map M).obj a`, before the
canonical base-projection transport returns from the universe-closed base to `C`.

This is deterministic comparison data, not an auxiliary existential choice. Naming it keeps the
structural-isomorphism formulas for `map` free of statement-local `let` bindings and gives
downstream calculations direct access to its two entries and comparison isomorphism. -/
@[stacks 0H2E "intermediate object of the pseudo-pullback comparison"]
noncomputable def map.comparisonObj
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {A : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    (M : A ⟶ CategoryTheory.TwoFibreProduct.apex
      X.baseProjection X.baseProjection) (a : A.total) :=
  (BasedCategory.PseudoPullback.Comparison.functor
      (FiberedCategoryOver.Groupoids.toBasedFunctor X.baseProjection)
      (FiberedCategoryOver.Groupoids.toBasedFunctor X.baseProjection)).obj
    ((FiberedCategoryOver.Groupoids.toFunctor M).obj a)

/-- The left projection of `map M` is the underlying functor of the
left owner composite.

Proof strategy: use BaseProjection.pullbackDown_fst, the left-projection comparison of
`BasedCategory.PseudoPullback.Comparison.functor`, and associativity of underlying functors. -/
@[simp] theorem map.fst
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {A : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    (M : A ⟶ CategoryTheory.TwoFibreProduct.apex
      X.baseProjection X.baseProjection) :
    map M ⋙ π₁ X.p X.p =
      FiberedCategoryOver.Groupoids.toFunctor
        (M ≫ (CategoryTheory.TwoFibreProduct.cone
          X.baseProjection X.baseProjection).fst) := sorry

/-- The right projection of `map M` is the underlying functor of the
right owner composite.

Proof strategy: use BaseProjection.pullbackDown_snd, the right-projection comparison of
`BasedCategory.PseudoPullback.Comparison.functor`, and associativity of underlying functors. -/
@[simp] theorem map.snd
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {A : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    (M : A ⟶ CategoryTheory.TwoFibreProduct.apex
      X.baseProjection X.baseProjection) :
    map M ⋙ π₂ X.p X.p =
      FiberedCategoryOver.Groupoids.toFunctor
        (M ≫ (CategoryTheory.TwoFibreProduct.cone
          X.baseProjection X.baseProjection).snd) := sorry

/-- Objectwise, the first projection of `map M` is the underlying left owner composite. -/
@[simp] theorem map.obj.fst
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {A : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    (M : A ⟶ CategoryTheory.TwoFibreProduct.apex
      X.baseProjection X.baseProjection) (a : A.total) :
    ((map M).obj a).fst =
      (FiberedCategoryOver.Groupoids.toFunctor
        (M ≫ (CategoryTheory.TwoFibreProduct.cone
          X.baseProjection X.baseProjection).fst)).obj a := sorry
/- Proof strategy: evaluate `map.fst M` at `a` and read the object component. -/

/-- Objectwise, the second projection of `map M` is the underlying right owner composite. -/
@[simp] theorem map.obj.snd
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {A : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    (M : A ⟶ CategoryTheory.TwoFibreProduct.apex
      X.baseProjection X.baseProjection) (a : A.total) :
    ((map M).obj a).snd =
      (FiberedCategoryOver.Groupoids.toFunctor
        (M ≫ (CategoryTheory.TwoFibreProduct.cone
          X.baseProjection X.baseProjection).snd)).obj a := sorry
/- Proof strategy: evaluate `map.snd M` at `a` and read the object component. -/

/-- On morphisms, the first projection of `map M` is the map of the underlying left owner
composite. -/
@[simp] theorem map.hom.fst
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {A : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    (M : A ⟶ CategoryTheory.TwoFibreProduct.apex
      X.baseProjection X.baseProjection)
    {a b : A.total} (f : a ⟶ b) :
    ((map M).map f).fst =
      (FiberedCategoryOver.Groupoids.toFunctor
        (M ≫ (CategoryTheory.TwoFibreProduct.cone
          X.baseProjection X.baseProjection).fst)).map f := sorry
/- Proof strategy: evaluate `map.fst M` on `f` and read the morphism component. -/

/-- On morphisms, the second projection of `map M` is the map of the underlying right owner
composite. -/
@[simp] theorem map.hom.snd
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {A : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    (M : A ⟶ CategoryTheory.TwoFibreProduct.apex
      X.baseProjection X.baseProjection)
    {a b : A.total} (f : a ⟶ b) :
    ((map M).map f).snd =
      (FiberedCategoryOver.Groupoids.toFunctor
        (M ≫ (CategoryTheory.TwoFibreProduct.cone
          X.baseProjection X.baseProjection).snd)).map f := sorry
/- Proof strategy: evaluate `map.snd M` on `f` and read the morphism component. -/

/-- Objectwise, the structural isomorphism of `map M` is the explicit pseudo-pullback
comparison mapped back from the universe-closed identity fibration to `C`. -/
@[simp] theorem map.obj.iso
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {A : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    (M : A ⟶ CategoryTheory.TwoFibreProduct.apex
      X.baseProjection X.baseProjection) (a : A.total) :
    ((map M).obj a).iso =
      ((FiberedCategoryOver.Groupoids.baseProjection.iso X).app
        (map.comparisonObj M a).fst).symm ≪≫
        (FiberedCategoryOver.Groupoids.base C).p.mapIso (map.comparisonObj M a).iso ≪≫
          (FiberedCategoryOver.Groupoids.baseProjection.iso X).app
            (map.comparisonObj M a).snd := sorry
/- Proof strategy: unfold only `map` as a composite, then apply
`BasedCategory.PseudoPullback.Comparison.functor.obj.iso` and
`BaseProjection.pullbackDown_obj_iso`. -/

/-- The forward map of the structural isomorphism carried by `map M` is the mapped
pseudo-pullback comparison conjugated by the base-projection comparisons. -/
@[simp] theorem map.obj.iso.hom
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {A : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    (M : A ⟶ CategoryTheory.TwoFibreProduct.apex
      X.baseProjection X.baseProjection) (a : A.total) :
    ((map M).obj a).iso.hom =
      (FiberedCategoryOver.Groupoids.baseProjection.iso X).inv.app
          (map.comparisonObj M a).fst ≫
        (FiberedCategoryOver.Groupoids.base C).p.map (map.comparisonObj M a).iso.hom ≫
          (FiberedCategoryOver.Groupoids.baseProjection.iso X).hom.app
            (map.comparisonObj M a).snd := sorry

/-- The inverse map of the structural isomorphism carried by `map M` is the reverse
conjugation of the inverse pseudo-pullback comparison. -/
@[simp] theorem map.obj.iso.inv
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {A : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    (M : A ⟶ CategoryTheory.TwoFibreProduct.apex
      X.baseProjection X.baseProjection) (a : A.total) :
    ((map M).obj a).iso.inv =
      (FiberedCategoryOver.Groupoids.baseProjection.iso X).inv.app
          (map.comparisonObj M a).snd ≫
        (FiberedCategoryOver.Groupoids.base C).p.map (map.comparisonObj M a).iso.inv ≫
          (FiberedCategoryOver.Groupoids.baseProjection.iso X).hom.app
            (map.comparisonObj M a).fst := sorry

end

end FiberedCategoryOver.Groupoids.PseudoPullbackComparison

end CategoryTheory
