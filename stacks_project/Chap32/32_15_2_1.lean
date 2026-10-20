/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.ValuativeCriterion
import StacksCheckRecall

universe u

open CategoryTheory

/- 32.15.2.1: the solid valuative square has maps `Spec(K) ⟶ X_α` and
`Spec(A) ⟶ S_α`, together with their canonical commutativity law. -/
@[stacks 05M0] #check
  (AlgebraicGeometry.ValuativeCommSq :
    {X S : AlgebraicGeometry.Scheme.{u}} → (X ⟶ S) → Type (u + 1))

section

variable {X S : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ S}
  (sq : AlgebraicGeometry.ValuativeCommSq f)

/- Existence of the dotted arrow `Spec(A) ⟶ X` is `HasLift` for the underlying square. -/
#check (CategoryTheory.CommSq.HasLift sq.commSq : Prop)

/- A chosen dotted arrow `Spec(A) ⟶ X` and its two triangle laws form a `LiftStruct`. -/
#check (CategoryTheory.CommSq.LiftStruct sq.commSq : Type u)

end
