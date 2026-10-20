/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.Basic
public import ReasLib.CategoryTheory.Fibered.InGroupoids
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Stacks in groupoids

A stack in groupoids over the site `(C, J)` is a category fibered in groupoids whose projection
is a stack over `(C, J)`. This packages the fiberwise groupoid condition (every fiber is a
groupoid, equivalently every morphism is Cartesian) together with the descent condition.

## Main declarations

* `CategoryTheory.IsStack.InGroupoids` — the stack-in-groupoids condition.
-/

@[expose] public section

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

variable {C : Type u₁} {S : Type u₂} [Category.{v₁} C] [Category.{v₂} S]

/-- A category over the site `(C, J)` is a stack in groupoids when its projection functor is
fibered in groupoids and its canonical fiber pseudofunctor satisfies descent. These are the two
independent canonical owners; the ordinary stack-on-site view is derived below. -/
@[stacks 02ZI]
class IsStack.InGroupoids (J : GrothendieckTopology C) (p : S ⥤ C) : Prop
    extends Functor.IsFibered.InGroupoids p,
      Pseudofunctor.IsStack (Functor.fiberPseudofunctor p) J

attribute [stacks 02ZI "stack-in-groupoids fibredness field"]
  IsStack.InGroupoids.toInGroupoids
attribute [stacks 02ZI "stack-in-groupoids pseudofunctor field"]
  IsStack.InGroupoids.toIsStack

/-- Forget the groupoid refinement while retaining the stack-on-site condition. -/
@[stacks 02ZI "stack-on-site view"]
theorem IsStack.InGroupoids.toOnSite
    {J : GrothendieckTopology C} {p : S ⥤ C} (h : IsStack.InGroupoids J p) :
    IsStack.OnSite J p := sorry

/-- A projection is a stack in groupoids exactly when it is a stack on the site and all its
standard fibers are groupoids. -/
@[stacks 02ZJ]
theorem IsStack.InGroupoids.iff_stackOnSite_and_fibersGroupoid
    (J : GrothendieckTopology C) (p : S ⥤ C) :
    IsStack.InGroupoids J p ↔
      IsStack.OnSite J p ∧ ∀ U : C, IsGroupoid (p.Fiber U) := sorry

/-- A projection is a stack in groupoids exactly when it is fibred in groupoids and is a stack
on the site. -/
@[stacks 02ZJ]
theorem IsStack.InGroupoids.iff_fibered_and_stackOnSite
    (J : GrothendieckTopology C) (p : S ⥤ C) :
    IsStack.InGroupoids J p ↔
      Functor.IsFibered.InGroupoids p ∧ IsStack.OnSite J p := sorry

/-- A fibered-in-groupoids functor that is already a stack over `(C, J)` is a stack in
groupoids. -/
@[stacks 02ZI "canonical stack-in-groupoids instance"]
instance IsStack.InGroupoids.ofOnSite (J : GrothendieckTopology C) (p : S ⥤ C)
    [Functor.IsFibered.InGroupoids p] [IsStack.OnSite J p] :
    IsStack.InGroupoids J p := sorry

end CategoryTheory
