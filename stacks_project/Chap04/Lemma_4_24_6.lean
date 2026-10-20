/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Adjunction.Exactness
import StacksCheckRecall

@[expose] public section

universe vC uC vD uD

namespace CategoryTheory.Adjunction

open CategoryTheory.Limits

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)

section

variable [HasFiniteColimits C]

/- Lemma 4.24.6 (1): a left adjoint from a finitely cocomplete category is right exact. -/
@[stacks 0039 "left adjoints are right exact"]
#check (adj.leftAdjoint_rightExact : rightExactFunctor C D L)

end

section

variable [HasFiniteLimits D]

/- Lemma 4.24.6 (2): a right adjoint from a finitely complete category is left exact. -/
@[stacks 0039 "right adjoints are left exact"]
#check (adj.rightAdjoint_leftExact : leftExactFunctor D C R)

end

end CategoryTheory.Adjunction
