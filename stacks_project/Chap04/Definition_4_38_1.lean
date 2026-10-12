/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Discrete.Basic
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

universe v u

variable (C : Type u) [Category.{v} C]

/-
Definition 4.38.1 (Stacks 02Y0): a category is discrete when its only morphisms are identity
morphisms. The canonical strict owner is `CategoryTheory.IsDiscrete`: its `subsingleton` field
makes every endomorphism equal to the identity, while `eq_of_hom` says that the endpoints of any
morphism are equal.

This strict, skeletal notion should not be transported across an arbitrary categorical
equivalence. The equivalence-invariant notion often called *essentially discrete* is instead a
groupoid with thin hom-spaces (`IsGroupoid C` together with `Quiver.IsThin C`), equivalently a
category equivalent to a `Discrete α`. Keeping the two notions separate prevents downstream
repleteness statements from silently asserting object equality across an equivalence.
-/
@[stacks 02Y0 "discrete categories"]
#check (IsDiscrete C : Prop)

end CategoryTheory
