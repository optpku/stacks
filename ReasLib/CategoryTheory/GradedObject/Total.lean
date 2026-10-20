/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import ReasLib.CategoryTheory.GradedObject.Instances

/-!
# Exactness of the total functor on graded objects

For a discrete grading type, exactness of the canonical shape-level coproduct functor
`Sigma.functor β : GradedObject β C ⥤ C` is controlled by exactness of the corresponding
coproducts.  A countably infinite grading therefore detects countable `AB4`.  Unlike
`GradedObject.total`, this formulation requires only the coproducts of the grading shape.
-/

@[expose] public section

open CategoryTheory.Limits

universe v u

namespace CategoryTheory.GradedObject

variable (β : Type) (C : Type u) [Category.{v} C] [Abelian C]

/-- The total functor is left exact exactly when coproducts indexed by the grading type are exact. -/
theorem leftExact_total_iff [HasCoproductsOfShape β C] :
    leftExactFunctor (GradedObject β C) C (Sigma.functor β) ↔
      HasExactColimitsOfShape (Discrete β) C := sorry

/-- For a countably infinite grading type, left exactness of the total functor is equivalent to
countable `AB4`. -/
theorem leftExact_total_iff_countableAB4 [HasCountableCoproducts C] [Countable β] [Infinite β] :
    leftExactFunctor (GradedObject β C) C (Sigma.functor β) ↔ CountableAB4 C := sorry

/-- For a countably infinite grading type, exactness of the total functor is equivalent to
countable `AB4`. -/
@[stacks 0AMH]
theorem exact_total_iff_countableAB4 [HasCountableCoproducts C] [Countable β] [Infinite β] :
    exactFunctor (GradedObject β C) C (Sigma.functor β) ↔ CountableAB4 C := sorry

/-- If countable coproducts are not exact, neither is the total functor for any countably infinite
grading type. -/
theorem not_exact_total_of_not_countableAB4 [HasCountableCoproducts C] [Countable β] [Infinite β]
    (h : ¬ CountableAB4 C) :
    ¬ exactFunctor (GradedObject β C) C (Sigma.functor β) := sorry

end CategoryTheory.GradedObject
