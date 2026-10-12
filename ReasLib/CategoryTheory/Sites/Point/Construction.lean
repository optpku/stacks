/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Functor.TypeValuedFlat
public import Mathlib.CategoryTheory.Sites.Point.Basic

/-!
# Constructing site points from fiber functors

This module isolates the cover-lifting condition on a `Type`-valued functor and
the resulting construction of a `GrothendieckTopology.Point`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u v w

namespace CategoryTheory.GrothendieckTopology.Point.Fiber

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Every element of a `J`-covering sieve lifts along one of its arrows through the
`Type`-valued functor `u`. -/
def coversLift (J : GrothendieckTopology C) (u : C ⥤ Type w) : Prop :=
  ∀ {X : C} (R : Sieve X), R ∈ J X → ∀ x : u.obj X,
    ∃ (Y : C) (f : Y ⟶ X) (_ : R f) (y : u.obj Y), u.map f y = x

/-- The concrete terminal-object and pullback condition which ensures that the category of
elements of a `Type`-valued functor is cofiltered. -/
def CofilteredElementsCondition [HasTerminal C] [HasPullbacks C]
    (u : C ⥤ Type w) : Prop :=
  (Subsingleton (u.obj (⊤_ C)) ∧ Nonempty (u.obj (⊤_ C))) ∧
    ∀ {U V W : C} (f : U ⟶ W) (g : V ⟶ W),
      Function.Surjective (pullbackComparison u f g)

/-- A `Type`-valued fiber satisfies the concrete point conditions when its terminal
fiber is unique, its pullback comparisons are surjective, and covering sieves lift
fiber elements. -/
@[stacks 00YD]
def IsPointFiber [HasTerminal C] [HasPullbacks C]
    (J : GrothendieckTopology C) (u : C ⥤ Type w) : Prop :=
  CofilteredElementsCondition u ∧ coversLift J u

/-- The fiber functor of a site point satisfies the cover-lifting condition. -/
theorem coversLift_of_point (p : GrothendieckTopology.Point.{w} J) :
    coversLift J p.fiber := sorry

/-- The concrete terminal-object and pullback condition makes the category of elements
cofiltered. -/
theorem isCofiltered_elements_of_condition [HasTerminal C] [HasPullbacks C]
    {u : C ⥤ Type w} (hu : CofilteredElementsCondition u) :
    IsCofiltered u.Elements := sorry

/-- The fiber functor of a site point satisfies the terminal-object and pullback part of the
concrete point-fiber condition. -/
theorem cofilteredElementsCondition_of_point [HasTerminal C] [HasPullbacks C]
    (p : GrothendieckTopology.Point.{w} J) :
    CofilteredElementsCondition p.fiber := sorry

/-- A site point fiber satisfies the reusable concrete point-fiber condition. -/
theorem isPointFiber_of_point [HasTerminal C] [HasPullbacks C]
    (p : GrothendieckTopology.Point.{w} J) :
    IsPointFiber J p.fiber := sorry

section

variable [HasFiniteLimits C]

/-- The canonical site point associated to a left exact `Type`-valued functor satisfying
cover lifting. -/
noncomputable def ofCoversLift
    (u : C ⥤ Type (max u v)) [PreservesFiniteLimits u] (h : coversLift J u) :
    GrothendieckTopology.Point.{max u v} J where
  fiber := u
  isCofiltered := Functor.isCofiltered_elements u
  initiallySmall := initiallySmall_of_essentiallySmall u.Elements
  jointly_surjective := h

/-- The fiber of `ofCoversLift` is the functor used in its construction. -/
@[simp]
theorem ofCoversLift_fiber
    (u : C ⥤ Type (max u v)) [PreservesFiniteLimits u] (h : coversLift J u) :
    (ofCoversLift u h).fiber = u := sorry

/-- A `Type`-valued functor on a site with finite limits underlies a site point
exactly when it preserves finite limits and lifts elements along covering sieves. -/
@[stacks 00YC]
theorem exists_iff (u : C ⥤ Type (max u v)) :
    (∃ p : GrothendieckTopology.Point.{max u v} J, p.fiber = u) ↔
      PreservesFiniteLimits u ∧ coversLift J u := sorry

end

end CategoryTheory.GrothendieckTopology.Point.Fiber
