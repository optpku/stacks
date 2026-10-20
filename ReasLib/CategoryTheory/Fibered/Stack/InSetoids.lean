module

public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoids
public import ReasLib.CategoryTheory.Fibered.InSetoids
public import ReasLib.CategoryTheory.Fibered.DiscreteFibration
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Stacks in setoids and stacks in sets

A stack in setoids stores the stack condition together with the intrinsic
fibered-in-setoids condition. A stack in sets instead stores the stack condition together with
the stronger discrete-fibration condition. Their stack-in-groupoids views are derived, avoiding
duplicated superclass paths.

## Main declarations

* `CategoryTheory.IsStack.InSetoids` — stack in groupoids with thin-groupoid fibers.
* `CategoryTheory.IsStack.InSets` — stack in groupoids with discrete fibers.
-/

@[expose] public section

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

variable {C : Type u₁} {S : Type u₂} [Category.{v₁} C] [Category.{v₂} S]
variable (J : GrothendieckTopology C) (p : S ⥤ C)

/-- A stack in setoids over the site `(C, J)` is a stack in groupoids whose fibers are thin
groupoids (equivalently, whose projection is faithful). The canonical owner stores the intrinsic
fibered-in-setoids condition and descent, without a second copy of ordinary fibredness. -/
@[stacks 042Z "stacks in setoids"]
class IsStack.InSetoids (J : GrothendieckTopology C) (p : S ⥤ C) : Prop
    extends Functor.IsFibered.InSetoids p,
      Pseudofunctor.IsStack (Functor.fiberPseudofunctor p) J

attribute [stacks 042Z "stack-in-setoids fibredness field"]
  IsStack.InSetoids.toInSetoids
attribute [stacks 042Z "stack-in-setoids pseudofunctor field"]
  IsStack.InSetoids.toIsStack

attribute [instance] IsStack.InSetoids.toInSetoids

/-- Forget the setoid refinement while retaining the stack-on-site condition. -/
@[stacks 042Z "stack-in-setoids site condition"]
theorem IsStack.InSetoids.toOnSite
    {J : GrothendieckTopology C} {p : S ⥤ C} (h : IsStack.InSetoids J p) :
    IsStack.OnSite J p := sorry

/-- The minimal owner for a stack in setoids consists of the stack condition and the intrinsic
fibered-in-setoids condition. -/
@[stacks 042Z "stack-in-setoids defining predicate"]
theorem IsStack.InSetoids.iff_fibered_and_stackOnSite :
    IsStack.InSetoids J p ↔ Functor.IsFibered.InSetoids p ∧ IsStack.OnSite J p := sorry

/-- A projection is a stack in setoids exactly when it is a stack on the site and every standard
fiber is a thin groupoid.  This is the source-facing fiberwise form of the intrinsic predicate. -/
@[stacks 042Z "stack-in-setoids fiberwise criterion"]
theorem IsStack.InSetoids.iff_stackOnSite_and_fibersSetoid :
    IsStack.InSetoids J p ↔
      IsStack.OnSite J p ∧
        ∀ U : C, IsGroupoid (p.Fiber U) ∧ Quiver.IsThin (p.Fiber U) := sorry

/-- A stack in setoids is equivalently a stack in groupoids with thin-groupoid fibers. -/
@[stacks 042Z "stack-in-setoids groupoid criterion"]
theorem IsStack.InSetoids.iff_fibered_and_groupoids :
    IsStack.InSetoids J p ↔ Functor.IsFibered.InSetoids p ∧ IsStack.InGroupoids J p := sorry

/-- For a projection already known to be fibered in setoids, being a stack in setoids is
equivalent to its underlying stack-on-site condition. -/
@[stacks 042Z "stack-in-setoids site criterion under fibredness"]
theorem IsStack.InSetoids.iff_isStackOnSite [Functor.IsFibered.InSetoids p] :
    IsStack.InSetoids J p ↔ IsStack.OnSite J p := sorry

/-- A stack in groupoids that is fibered in setoids is a stack in setoids. -/
@[stacks 042Z "stack-in-setoids canonical instance"]
instance [Functor.IsFibered.InSetoids p] [IsStack.OnSite J p] :
    IsStack.InSetoids J p := sorry

/-- A stack in sets over `(C, J)` is a stack in groupoids whose fibers are discrete
(equivalently, whose projection is a discrete fibration). The canonical owner stores the
discrete-fibration condition and descent, without rebuilding its derived fibredness. -/
@[stacks 042Z "stacks in sets"]
class IsStack.InSets (J : GrothendieckTopology C) (p : S ⥤ C) : Prop
    extends Functor.IsDiscreteFibration p,
      Pseudofunctor.IsStack (Functor.fiberPseudofunctor p) J

attribute [stacks 042Z "stack-in-sets discrete-fibration field"]
  IsStack.InSets.toIsDiscreteFibration
attribute [stacks 042Z "stack-in-sets pseudofunctor field"]
  IsStack.InSets.toIsStack

/-- Forget the discrete refinement while retaining the stack-on-site condition. -/
@[stacks 042Z "stack-in-sets site condition"]
theorem IsStack.InSets.toOnSite
    {J : GrothendieckTopology C} {p : S ⥤ C} (h : IsStack.InSets J p) :
    IsStack.OnSite J p := sorry

/-- The minimal owner for a stack in sets consists of the stack condition and the intrinsic
discrete-fibration condition. -/
@[stacks 042Z "stack-in-sets defining predicate"]
theorem IsStack.InSets.iff_discreteFibration_and_stackOnSite :
    IsStack.InSets J p ↔ Functor.IsDiscreteFibration p ∧ IsStack.OnSite J p := sorry

/-- A projection is a stack in sets exactly when it is a stack on the site and every standard
fiber is discrete. -/
@[stacks 042Z "stack-in-sets fiberwise criterion"]
theorem IsStack.InSets.iff_stackOnSite_and_fibersDiscrete :
    IsStack.InSets J p ↔
      IsStack.OnSite J p ∧ ∀ U : C, IsDiscrete (p.Fiber U) := sorry

/-- For a projection already known to be a discrete fibration, being a stack in sets is
equivalent to the underlying stack-on-site condition. -/
@[stacks 042Z "stack-in-sets site criterion under discreteness"]
theorem IsStack.InSets.iff_isStackOnSite [Functor.IsDiscreteFibration p] :
    IsStack.InSets J p ↔ IsStack.OnSite J p := sorry

/-- A discrete fibration satisfying the stack condition is a stack in sets. -/
@[stacks 042Z "stack-in-sets canonical instance"]
instance [Functor.IsDiscreteFibration p] [IsStack.OnSite J p] :
    IsStack.InSets J p := sorry

/-- A stack in sets is a stack in setoids. -/
@[stacks 042Z "stack-in-sets to stack-in-setoids"]
instance [IsStack.InSets J p] : IsStack.InSetoids J p := sorry

section

variable [IsStack.InSetoids J p]

#synth IsStack.InGroupoids J p
#synth IsStack.OnSite J p
#synth Functor.IsFibered.InSetoids p

end

section

variable [IsStack.InSets J p]

#synth IsStack.InSetoids J p
#synth Functor.IsDiscreteFibration p

end

end CategoryTheory
