module

public import Mathlib.CategoryTheory.Abelian.Basic
import StacksCheckRecall

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C]

/- Lemma 12.5.5 (1): every abelian category has all finite limits. -/
@[stacks 010D] #check
  (Abelian.hasFiniteLimits : HasFiniteLimits C)

/- Lemma 12.5.5 (2): every abelian category has all finite colimits. -/
#check (Abelian.hasFiniteColimits : HasFiniteColimits C)

end CategoryTheory
