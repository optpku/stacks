module

public import ReasLib.CategoryTheory.Fibered.Inertia.Sets.AbsolutePseudofunctor.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Projection.Objects.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Set-fibred inertia object constructions

This leaf owns the bundled relative and absolute inertia data in the strict
discrete-fibration owner. Projection and neutral-owner computations live in
`Objects.Computations`.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor
open scoped Bicategory

namespace FiberedCategoryOver.Sets

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.Sets.{u, v, w, vS} C}

namespace Implementation

set_option backward.privateInPublic true in
/-- The neutral relative-inertia based category satisfies the strict discrete-fibration owner
property when both endpoints do. -/
private theorem relative_mem (F : X ⟶ Y) :
    BasedCategory.isFiberedInSets C
      (BasedCategory.relativeInertia (toBasedFunctor F)) := sorry

end Implementation

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Definition 4.34.2 (1) (Stacks 034I): relative inertia of a morphism between categories
fibred in sets. The carrier and projection are exactly the neutral relative-inertia data; only
the discrete-fibration membership is added. -/
@[stacks 034I "relative inertia of a set-fibred morphism"]
def relativeInertia (F : X ⟶ Y) :
    FiberedCategoryOver.Sets.{u, v, max w vS, vS} C :=
  ⟨BasedCategory.relativeInertia (toBasedFunctor F),
    Implementation.relative_mem F⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Definition 4.34.2 (2) (Stacks 034I): absolute inertia of a category fibred in sets. -/
@[stacks 034I "absolute inertia of a set-fibred category"]
def inertia (X : FiberedCategoryOver.Sets.{u, v, w, vS} C) :
    FiberedCategoryOver.Sets.{u, v, max w vS, vS} C :=
  (Inertia.strictPseudofunctor C).obj X

end FiberedCategoryOver.Sets

end CategoryTheory
