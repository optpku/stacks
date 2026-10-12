/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Limits.FiniteConnected.Basic
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory.Limits

universe v u

variable (C : Type u) [Category.{v} C]

/- Lemma 4.18.2: a category has limits of every finite connected small diagram if and only if it
has equalizers and fibre products. -/
@[stacks 04AT]
#check (HasFiniteConnectedLimits.Pullbacks.iff_equalizers C :
  HasFiniteConnectedLimits C ↔ HasEqualizers C ∧ HasPullbacks C)

end CategoryTheory.Limits
