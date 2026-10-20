/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.CategoryOver.Fiber
public import ReasLib.CategoryTheory.Fibered.Inertia.Based.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.DiagonalComparison.Equivalence.Construction
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Cartesian
import Mathlib.Tactic.CrossRefAttribute

/-!
# Relative inertia projection fibredness

This leaf owns the intrinsic fibredness closure for relative-inertia projections.
-/

@[expose] public section

universe u v uX vX uY vY

namespace CategoryTheory

open BasedCategory BasedFunctor

namespace RelativeInertia

namespace Projection

namespace Fibered

variable {C : Type u} [Category.{v} C]
variable {S : Type uX} [Category.{vX} S]
variable {S' : Type uY} [Category.{vY} S']
variable {p : S ⥤ C} {p' : S' ⥤ C}

/-- The relative-inertia projection of a cartesian functor between fibred categories is fibred. -/
@[stacks 034H "relative-inertia projection fibredness from a cartesian functor"]
theorem ofCartesian
    [p.IsFibered] (F : CartesianBasedFunctor p p') :
    (RelativeInertia.projection F.toFunctor p).IsFibered := sorry
/- Proof strategy: compare relative inertia with the self-pseudo-pullback of the relative
diagonal, use fibredness of the explicit pseudo-pullback projection, and transport it across
`BasedFunctor.RelativeInertia.diagonalComparison.isEquivalence`. -/

/-- The self-relative-inertia projection of a fibred functor is fibred. -/
@[stacks 034H "self-relative-inertia projection fibredness"]
theorem self (p : S ⥤ C) [p.IsFibered] :
    (RelativeInertia.projection p p).IsFibered := sorry
/- Proof strategy: pull a vertical automorphism back along a strongly cartesian lift in `p`;
strong-cartesian uniqueness constructs its inverse and proves the required universal property. -/

end Fibered

end Projection

end RelativeInertia

end CategoryTheory
