module

public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Chosen strongly cartesian lifts

Mathlib's `IsPreFibered.pullbackMap` supplies the canonical chosen cartesian lift of a base
morphism.  For a fibred projection this lift is strongly cartesian; the named instance here is
the reusable boundary between the chosen-lift construction and downstream cleavage or pullback
arguments.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory.Functor.IsPreFibered.PullbackMap

variable {C : Type u} [Category.{v} C]
variable {S : Type w} [Category.{vS} S]

/-- Mathlib's chosen cartesian pullback arrow is strongly cartesian when the projection is
fibred. -/
@[stacks 02XN "canonical chosen strongly cartesian lift"]
instance stronglyCartesian
    (p : S ⥤ C) [p.IsFibered] {x : S} {V : C} (f : V ⟶ p.obj x) :
    p.IsStronglyCartesian f (IsPreFibered.pullbackMap rfl f) :=
  Functor.IsFibered.isStronglyCartesian_of_isCartesian p f
    (IsPreFibered.pullbackMap rfl f)

end CategoryTheory.Functor.IsPreFibered.PullbackMap
