/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Pointwise Derived Functors and Denominators

This leaf records the denominator-inversion API shared by pointwise left and right derived
functors. It is formulated for an arbitrary localization class, independently of any concrete
model of a derived category.
-/

universe vC vH uC uH

namespace CategoryTheory.Functor

variable {C : Type uC} {H : Type uH}
  [Category.{vC} C] [Category.{vH} H]
  (W : MorphismProperty C) (F : C ⥤ H)

/-- Stacks 05SB: the total pointwise right derived functor inverts every morphism in its
localization class. -/
@[stacks 05SB]
theorem totalRightDerived_isInvertedBy [F.HasPointwiseRightDerivedFunctor W] :
    W.IsInvertedBy (W.Q ⋙ F.totalRightDerived W.Q W) := sorry

/-- Stacks 05SB: a denominator is sent to an isomorphism by the total pointwise right derived
functor. -/
@[stacks 05SB]
theorem totalRightDerived_map_isIso_of_mem {X Y : C} (w : X ⟶ Y) (hw : W w)
    [F.HasPointwiseRightDerivedFunctor W] :
    IsIso ((F.totalRightDerived W.Q W).map (W.Q.map w)) := sorry

/-- Stacks 05SB: the total pointwise left derived functor inverts every morphism in its
localization class. -/
@[stacks 05SB]
theorem totalLeftDerived_isInvertedBy [F.HasPointwiseLeftDerivedFunctor W] :
    W.IsInvertedBy (W.Q ⋙ F.totalLeftDerived W.Q W) := sorry

/-- Stacks 05SB: a denominator is sent to an isomorphism by the total pointwise left derived
functor. -/
@[stacks 05SB]
theorem totalLeftDerived_map_isIso_of_mem {X Y : C} (w : X ⟶ Y) (hw : W w)
    [F.HasPointwiseLeftDerivedFunctor W] :
    IsIso ((F.totalLeftDerived W.Q W).map (W.Q.map w)) := sorry

end CategoryTheory.Functor
