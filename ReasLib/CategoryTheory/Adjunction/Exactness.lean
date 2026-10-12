/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.ExactFunctor

/-!
# Exactness consequences of adjunctions

Left adjoints are right exact when the source has finite colimits, and right adjoints are left
exact when the source of the right adjoint has finite limits.
-/

@[expose] public section

open CategoryTheory.Limits

universe vC uC vD uD

namespace CategoryTheory.Adjunction

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {L : C ⥤ D} {R : D ⥤ C}

/-- A left adjoint from a finitely cocomplete category is right exact. -/
@[stacks 0039 "left adjoints are right exact", stacks 01AJ "(2)"]
theorem leftAdjoint_rightExact [HasFiniteColimits C] (adj : L ⊣ R) :
    rightExactFunctor C D L := sorry

/-- A right adjoint from a finitely complete category is left exact. -/
@[stacks 0039 "right adjoints are left exact", stacks 01AJ "(1)"]
theorem rightAdjoint_leftExact [HasFiniteLimits D] (adj : L ⊣ R) :
    leftExactFunctor D C R := sorry

end CategoryTheory.Adjunction
