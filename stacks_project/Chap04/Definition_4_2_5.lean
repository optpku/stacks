/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Groupoid
import StacksCheckRecall

@[expose] public section
universe v u

namespace CategoryTheory

variable (C : Type u)

/- The source defines the bundled notion of a groupoid. `Groupoid` is the exact canonical owner: it
extends `Category` with inverse data and laws, and supplies `IsIso` for every morphism. `IsGroupoid`
is instead the Prop-valued condition on an already fixed category, with `Groupoid.ofIsGroupoid` as
its noncomputable bridge to bundled data. Recalling `Groupoid` introduces no generalization and
gives downstream users the standard inverse and isomorphism APIs without parallel local packaging. -/

/- Definition 4.2.5: a groupoid is a category in which every morphism is an isomorphism; this is
the defining content bundled by the canonical mathlib class `Groupoid`. -/
@[stacks 0018 "groupoid structure"]
#check (Groupoid.{v} C : Type max u (v + 1))

end CategoryTheory
