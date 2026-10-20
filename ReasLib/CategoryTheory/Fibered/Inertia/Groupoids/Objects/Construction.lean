/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.Closure.Projection
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.AbsolutePseudofunctor.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Projection.Objects.Construction
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom
import Mathlib.Tactic.CrossRefAttribute

/-!
# Groupoid-fibred inertia object constructions

This leaf owns the bundled groupoid-fibred relative and absolute inertia data.
Projection and neutral-owner computations live in `Objects.Computations`.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor

namespace FiberedCategoryOver.Groupoids

open scoped Bicategory

variable {C : Type u} [Category.{v} C]

section GeneralInertia

variable {X Y : FiberedCategoryOver.Groupoids.{u, v, w, vS} C}

namespace Implementation

set_option backward.privateInPublic true in
/-- The neutral relative-inertia based category satisfies the groupoid-fibration owner
property. -/
private theorem relative_mem (F : X ⟶ Y) :
    BasedCategory.isFiberedInGroupoids C
      (BasedCategory.relativeInertia (toBasedFunctor F)) := sorry
/- Proof strategy: use `RelativeInertia.Projection.Groupoids.ofCartesian`; every morphism into a
groupoid-fibred target preserves strongly cartesian arrows. -/

end Implementation

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Definition 4.34.2 (1) (Stacks 034I): relative inertia of a morphism between categories
fibred in groupoids. Its underlying based category is the neutral universe-changing
`BasedCategory.relativeInertia` construction. -/
@[stacks 034I "relative inertia of a groupoid-fibred morphism"]
def relativeInertia (F : X ⟶ Y) :
    FiberedCategoryOver.Groupoids.{u, v, max w vS, vS} C :=
  ⟨BasedCategory.relativeInertia (toBasedFunctor F),
    Implementation.relative_mem F⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Definition 4.34.2 (2) (Stacks 034I): absolute inertia of a category fibred in groupoids.
Its underlying based category is the neutral universe-changing `BasedCategory.inertia`
construction. -/
@[stacks 034I "absolute inertia of a groupoid-fibred category"]
abbrev inertia
    (X : FiberedCategoryOver.Groupoids.{u, v, w, vS} C) :
    FiberedCategoryOver.Groupoids.{u, v, max w vS, vS} C :=
  (Inertia.strictPseudofunctor C).obj X

/- Axiom audit: `#print axioms` reports `propext`, `Classical.choice`, `Quot.sound`, and
`sorryAx`. The `sorryAx` dependency is confined to the Prop-valued groupoid-fibration membership
witness used by `Inertia.strictPseudofunctor`; the underlying based inertia object and its
projection are explicit neutral data. -/

end GeneralInertia

end FiberedCategoryOver.Groupoids

end CategoryTheory
