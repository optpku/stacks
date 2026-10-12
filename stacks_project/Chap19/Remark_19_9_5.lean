/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Abelian.FreydMitchell
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

universe v u

variable (C : Type u) [Category.{v} C] [Abelian C]

/- Remark 19.9.5: the construction sketched here recovers the canonical mathlib
Freyd-Mitchell theorem: every abelian category admits a full, faithful, exact embedding into a
module category. Exactness is expressed by preservation of finite limits and finite colimits. -/
@[stacks 05PR] #check
  (freyd_mitchell C :
    ∃ (R : Type (max u v)) (_ : Ring R) (F : C ⥤ ModuleCat.{max u v} R),
      F.Full ∧ F.Faithful ∧ PreservesFiniteLimits F ∧ PreservesFiniteColimits F)
