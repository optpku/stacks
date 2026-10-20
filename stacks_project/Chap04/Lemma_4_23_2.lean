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

variable {C : Type uC} [Category.{vC} C] [HasFiniteLimits C]
variable {D : Type uD} [Category.{vD} D]
variable (F : C ⥤ D)

/- Lemma 4.23.2 (1): finite products and equalizers characterize left exactness. -/
@[stacks 0035 "finite products and equalizers characterize left exactness"]
#check (leftExactFunctor.iff_preservesFiniteProducts_and_equalizers F :
  leftExactFunctor C D F ↔
    PreservesFiniteProducts F ∧ PreservesLimitsOfShape WalkingParallelPair F)

/- Lemma 4.23.2 (2): terminal objects and pullbacks characterize left exactness. -/
@[stacks 0035 "terminal objects and pullbacks characterize left exactness"]
#check (leftExactFunctor.iff_preservesTerminal_and_pullbacks F :
  leftExactFunctor C D F ↔
    PreservesLimit (Functor.empty.{0} C) F ∧ PreservesLimitsOfShape WalkingCospan F)

end CategoryTheory
