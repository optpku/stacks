/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.Exactness
import StacksCheckRecall

@[expose] public section

universe vC uC vD uD

namespace CategoryTheory

open Limits

variable {C : Type uC} [Category.{vC} C] [HasFiniteColimits C]
variable {D : Type uD} [Category.{vD} D]
variable (F : C ⥤ D)

/- Lemma 4.23.3 (1): finite coproducts and coequalizers characterize right exactness. -/
@[stacks 0GMN "finite coproducts and coequalizers characterize right exactness"]
#check (rightExactFunctor.iff_preservesFiniteCoproducts_and_coequalizers F :
  rightExactFunctor C D F ↔
    PreservesFiniteCoproducts F ∧ PreservesColimitsOfShape WalkingParallelPair F)

/- Lemma 4.23.3 (2): initial objects and pushouts characterize right exactness. -/
@[stacks 0GMN "initial objects and pushouts characterize right exactness"]
#check (rightExactFunctor.iff_preservesInitial_and_pushouts F :
  rightExactFunctor C D F ↔
    PreservesColimit (Functor.empty.{0} C) F ∧ PreservesColimitsOfShape WalkingSpan F)

end CategoryTheory
