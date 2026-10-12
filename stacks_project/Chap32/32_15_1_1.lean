/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.AlgebraicGeometry.ValuativeCriterion
import StacksCheckRecall

open CategoryTheory

universe u

/- 32.15.1.1: `AlgebraicGeometry.ValuativeCommSq f` is the solid commutative square
from `Spec K` and `Spec A` associated to a valuation ring `A` with fraction field `K`.
A prospective dotted morphism `Spec A ⟶ X` is a lift of its underlying commutative square. -/
@[stacks 0206] #check
  (AlgebraicGeometry.ValuativeCommSq :
    {X S : AlgebraicGeometry.Scheme.{u}} → (X ⟶ S) → Type (u + 1))

section

variable {X S : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ S}
variable (sq : AlgebraicGeometry.ValuativeCommSq f)

-- A chosen dotted morphism together with the two triangle identities.
#check sq.commSq.LiftStruct

-- The proposition that such a dotted morphism exists.
#check sq.commSq.HasLift

end
