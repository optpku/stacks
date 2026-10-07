module

public import ReasLib.CategoryTheory.Fibered.Inertia.Setoids.Closure.Projection
public import ReasLib.CategoryTheory.Fibered.Inertia.Setoids.AbsolutePseudofunctor.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Projection.Objects.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Setoid-fibred inertia object constructions

This leaf owns the bundled setoid-fibred relative and absolute inertia data.
Projection and neutral-owner computations live in `Objects.Computations`.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor

namespace FiberedCategoryOver.Setoids

open scoped Bicategory Pseudofunctor.StrongTrans

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.Setoids.{u, v, w, vS} C}

namespace Implementation

set_option backward.privateInPublic true in
/-- Neutral relative inertia of a morphism between setoid-fibred categories again satisfies the
setoid-fibration owner property. -/
private theorem relative_mem (F : X ⟶ Y) :
    BasedCategory.isFiberedInSetoids C
      (BasedCategory.relativeInertia (toBasedFunctor F)) := sorry
/- Proof strategy: combine `RelativeInertia.Projection.Setoids.ofCartesian` with the automatic
strong-cartesian preservation of a based functor into a groupoid-fibred target. -/

end Implementation

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Definition 4.34.2 (1) (Stacks 034I): relative inertia in the full subbicategory of
categories fibred in setoids. Its underlying based category is the neutral
`BasedCategory.relativeInertia`; only the Prop-valued owner membership is added. -/
@[stacks 034I "relative inertia of a setoid-fibred morphism"]
def relativeInertia (F : X ⟶ Y) :
    FiberedCategoryOver.Setoids.{u, v, max w vS, vS} C :=
  ⟨BasedCategory.relativeInertia (toBasedFunctor F),
    Implementation.relative_mem F⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Definition 4.34.2 (2) (Stacks 034I): absolute inertia in the full subbicategory of
categories fibred in setoids. Its underlying based category is the neutral universe-changing
`BasedCategory.inertia` construction. -/
@[stacks 034I "absolute inertia of a setoid-fibred category"]
abbrev inertia (X : FiberedCategoryOver.Setoids.{u, v, w, vS} C) :
    FiberedCategoryOver.Setoids.{u, v, max w vS, vS} C :=
  (Inertia.strictPseudofunctor C).obj X

/- Axiom audit: the non-Prop total categories and projections of `relativeInertia` and `inertia`
are the corresponding neutral based constructions. Any `sorryAx` enters only through the
Prop-valued setoid-fibration membership witnesses. -/

end FiberedCategoryOver.Setoids

end CategoryTheory
