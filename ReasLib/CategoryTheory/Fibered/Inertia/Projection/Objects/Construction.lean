/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Projection.Fiberedness.FiberedCategory
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fibred inertia object constructions

This module owns the bundled relative and absolute inertia objects.  Their
projection and total-category readout lemmas are provided by `Computations`.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open BasedCategory BasedFunctor

namespace FiberedCategoryOver

open scoped Bicategory

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.{u, v, w, vS} C}

namespace Implementation

set_option backward.privateInPublic true in
/-- The neutral based relative-inertia construction satisfies the fibred-category object
property. -/
private theorem relativeInertia_mem (F : X ⟶ Y) :
    BasedCategory.isFibered C
      (BasedCategory.relativeInertia (toBasedFunctor F)) := sorry
/- Proof strategy: unfold `BasedCategory.isFibered`, rewrite the projection with
`BasedCategory.relativeInertia.p`, and apply
`RelativeInertia.Projection.Fibered.ofCartesian`. -/

set_option backward.privateInPublic true in
/-- The neutral based absolute-inertia construction satisfies the fibred-category object
property. -/
private theorem inertia_mem (X : FiberedCategoryOver.{u, v, w, vS} C) :
    BasedCategory.isFibered C (BasedCategory.inertia X.toBasedCategory) := sorry
/- Proof strategy: unfold `BasedCategory.isFibered` and use
`BasedCategory.Inertia.Projection.Fibered.self`. -/

end Implementation

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Definition 4.34.2 (1) (Stacks 034I): the relative inertia over `C` attached to a morphism of
fibred categories. -/
@[stacks 034I "relative inertia of a morphism of fibred categories"]
def relativeInertia (F : X ⟶ Y) :
    FiberedCategoryOver.{u, v, max w vS, vS} C :=
  ⟨BasedCategory.relativeInertia (toBasedFunctor F),
    Implementation.relativeInertia_mem F⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Definition 4.34.2 (2) (Stacks 034I): absolute inertia of a fibred category, retained at
the fibred-category owner layer. Its non-Prop datum is exactly the canonical based absolute
inertia; only fibredness is added as an object-property witness. -/
@[stacks 034I "absolute inertia of a fibred category"]
def inertia (X : FiberedCategoryOver.{u, v, w, vS} C) :
    FiberedCategoryOver.{u, v, max w vS, vS} C :=
  ⟨BasedCategory.inertia X.toBasedCategory, Implementation.inertia_mem X⟩

end FiberedCategoryOver
end CategoryTheory
