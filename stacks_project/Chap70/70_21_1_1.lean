/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import stacks_project.Chap67.Definition_67_41_1_ValuativeCriterion
import StacksCheckRecall

open CategoryTheory

universe u

/- 70.21.1.1: `AlgebraicGeometry.AlgebraicSpace.ValuativeCommSq f` is the solid
commutative square of morphisms of algebraic spaces over a scheme `S`, with
vertices `Spec(K)`, `X`, `Spec(A)`, `Y`, associated to a valuation ring `A` with
fraction field `K`. A prospective dashed morphism `Spec(A) ⟶ X` is a lift of
its underlying commutative square. -/
@[stacks 0H1V] #check
  (AlgebraicGeometry.AlgebraicSpace.ValuativeCommSq :
    {S : AlgebraicGeometry.Scheme.{u}} → {X Y : AlgebraicGeometry.AlgebraicSpace S} →
      (X ⟶ Y) → Type (u + 1))

section

variable {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
variable {f : X ⟶ Y} (sq : AlgebraicGeometry.AlgebraicSpace.ValuativeCommSq f)

-- A chosen dashed morphism together with the two triangle identities.
#check sq.commSq.LiftStruct

-- The proposition that such a dashed morphism exists.
#check sq.commSq.HasLift

end
