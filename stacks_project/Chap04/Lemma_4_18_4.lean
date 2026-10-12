/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Limits.Finite
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory.Limits

universe v u

variable (C : Type u) [Category.{v} C]

/- Lemma 4.18.4: finite limits, finite products with equalizers, and a terminal object with
pullbacks are equivalent conditions. -/
@[stacks 002O]
#check (HasFiniteLimits.tfae C :
  [HasFiniteLimits C, HasFiniteProducts C ∧ HasEqualizers C,
    HasTerminal C ∧ HasPullbacks C].TFAE)

end CategoryTheory.Limits
