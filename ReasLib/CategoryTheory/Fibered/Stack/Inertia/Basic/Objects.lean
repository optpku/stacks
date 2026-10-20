module

import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Stable.Maps
import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Stable.Relative.Maps
public import ReasLib.CategoryTheory.Fibered.Inertia.Projection.Objects.Construction
public import ReasLib.CategoryTheory.Fibered.Stack.InSetoids
public import ReasLib.CategoryTheory.Fibered.Stack.Over
public import ReasLib.CategoryTheory.Fibered.Stack.Prestack
import Mathlib.Tactic.CrossRefAttribute

/-!
# Inertia objects of stacks

Closure of relative and absolute inertia under the stack conditions, and the corresponding
bundled `StackOver` objects. Computations comparing these owners with neutral fibered-category
owners are isolated in `Basic.Comparisons`.
-/

@[expose] public section

universe u v uX vX uY vY w vS

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace BasedCategory.Inertia

/-- Absolute inertia preserves the stack-on-site condition for an arbitrary based category
with fibred projection. -/
@[stacks 036Y "absolute inertia stack closure for based categories"]
theorem isStackOnSite
    (X : BasedCategory.{vS, w} C) [IsStack.OnSite J X.p] :
    IsStack.OnSite J (BasedCategory.inertia X).p := sorry

end BasedCategory.Inertia

namespace BasedCategory.RelativeInertia

variable {X : BasedCategory.{vX, uX} C}
variable {Y : BasedCategory.{vY, uY} C}

/-- Lemma 8.7.1 (1), relative part, tag 036Y, in the heterogeneous cartesian layer: relative
inertia is a stack when its source is a stack and its target is a prestack. -/
@[stacks 036Y "heterogeneous relative-inertia stack closure"]
theorem isStackOnSite
    [IsStack.OnSite J X.p] [IsPrestack.OnSite J Y.p]
    (F : CartesianBasedFunctor X.p Y.p) :
    IsStack.OnSite J (BasedCategory.relativeInertia F.toBasedFunctor).p := sorry

/-- Lemma 8.7.1 (2), relative part, tag 036Y, in the heterogeneous cartesian layer: relative
inertia is a stack in groupoids when its source is one and its target is a prestack. -/
@[stacks 036Y "heterogeneous relative-inertia groupoid closure"]
theorem isStackInGroupoids
    [IsStack.InGroupoids J X.p] [IsPrestack.OnSite J Y.p]
    (F : CartesianBasedFunctor X.p Y.p) :
    IsStack.InGroupoids J (BasedCategory.relativeInertia F.toBasedFunctor).p := sorry

/-- Lemma 8.7.1 (3), relative part, tag 036Y, in the heterogeneous cartesian layer: relative
inertia is a stack in setoids when its source is one and its target is a prestack. -/
@[stacks 036Y "heterogeneous relative-inertia setoid closure"]
theorem isStackInSetoids
    [IsStack.InSetoids J X.p] [IsPrestack.OnSite J Y.p]
    (F : CartesianBasedFunctor X.p Y.p) :
    IsStack.InSetoids J (BasedCategory.relativeInertia F.toBasedFunctor).p := sorry

end BasedCategory.RelativeInertia

namespace FiberedCategoryOver.RelativeInertia

variable {X Y : FiberedCategoryOver.{u, v, w, vS} C}

/-- Fixed-universe specialization of heterogeneous relative-inertia stack closure. -/
@[stacks 036Y "fixed-universe relative-inertia stack closure"]
theorem isStackOnSite
    [IsStack.OnSite J X.p] [IsPrestack.OnSite J Y.p] (F : X ⟶ Y) :
    IsStack.OnSite J (FiberedCategoryOver.relativeInertia F).p := sorry

/-- Fixed-universe specialization of heterogeneous relative-inertia groupoid-stack closure. -/
@[stacks 036Y "fixed-universe relative-inertia groupoid closure"]
theorem isStackInGroupoids
    [IsStack.InGroupoids J X.p] [IsPrestack.OnSite J Y.p] (F : X ⟶ Y) :
    IsStack.InGroupoids J (FiberedCategoryOver.relativeInertia F).p := sorry

/-- Fixed-universe specialization of heterogeneous relative-inertia setoid-stack closure. -/
@[stacks 036Y "fixed-universe relative-inertia setoid closure"]
theorem isStackInSetoids
    [IsStack.InSetoids J X.p] [IsPrestack.OnSite J Y.p] (F : X ⟶ Y) :
    IsStack.InSetoids J (FiberedCategoryOver.relativeInertia F).p := sorry

end FiberedCategoryOver.RelativeInertia

namespace FiberedCategoryOver.Inertia

/-- Absolute inertia preserves the stack-on-site condition. -/
@[stacks 036Y "fixed-universe absolute inertia stack closure"]
theorem isStackOnSite
    (X : FiberedCategoryOver.{u, v, w, vS} C) [IsStack.OnSite J X.p] :
    IsStack.OnSite J (FiberedCategoryOver.inertia X).p := sorry

/-- Absolute inertia preserves stacks in groupoids. -/
@[stacks 036Y "fixed-universe absolute inertia groupoid closure"]
theorem isStackInGroupoids
    (X : FiberedCategoryOver.{u, v, w, vS} C) [IsStack.InGroupoids J X.p] :
    IsStack.InGroupoids J (FiberedCategoryOver.inertia X).p := sorry

/-- Absolute inertia preserves stacks in setoids. -/
@[stacks 036Y "fixed-universe absolute inertia setoid closure"]
theorem isStackInSetoids
    (X : FiberedCategoryOver.{u, v, w, vS} C) [IsStack.InSetoids J X.p] :
    IsStack.InSetoids J (FiberedCategoryOver.inertia X).p := sorry

end FiberedCategoryOver.Inertia

namespace StackOver

variable {X Y : StackOver.{u, v, w, vS} J}

/-- The relative inertia of a morphism of stacks, bundled again as a stack over the same site. -/
@[stacks 036Y "relative inertia stack"]
def relativeInertia (F : X ⟶ Y) : StackOver.{u, v, max w vS, vS} J :=
  StackOver.mk
    (FiberedCategoryOver.relativeInertia (StackOver.Hom.toMor F))
    (FiberedCategoryOver.RelativeInertia.isStackOnSite
      (J := J) (StackOver.Hom.toMor F))

/-- The absolute inertia of a stack, bundled again as a stack over the same site. -/
@[stacks 036Y "absolute inertia stack"]
def inertia (X : StackOver.{u, v, w, vS} J) : StackOver.{u, v, max w vS, vS} J :=
  StackOver.mk
    (FiberedCategoryOver.inertia X.toFiberedCategoryOver)
    (FiberedCategoryOver.Inertia.isStackOnSite (J := J) X.toFiberedCategoryOver)

end StackOver

end CategoryTheory
