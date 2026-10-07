module

import stacks_project.Chap67.Definition_67_41_1_ValuativeCriterion
import StacksCheckRecall

universe u

open CategoryTheory AlgebraicGeometry

/- 67.42.5.1: `AlgebraicGeometry.AlgebraicSpace.ValuativeCommSq f` is the solid
commutative square `Spec(K) ⟶ X` over `Spec(A) ⟶ Y` associated to a valuation ring `A`
with fraction field `K`. Source `A` is the field `R` of this owner; the top arrow is `i₁`,
the bottom arrow is `i₂`, the left vertical arrow is `verticalMap`, and the right vertical
arrow is `f`. -/
@[stacks 089H] #check
  (AlgebraicGeometry.AlgebraicSpace.ValuativeCommSq :
    {S : AlgebraicGeometry.Scheme.{u}} → {X Y : AlgebraicGeometry.AlgebraicSpace S} →
      (X ⟶ Y) → Type (u + 1))

section

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
  (sq : AlgebraicSpace.ValuativeCommSq f)

-- Source A is sq.R; K is sq.K.
#check sq.R
#check sq.K
-- Top arrow Spec(K) ⟶ X.
#check sq.i₁
-- Bottom arrow Spec(A) ⟶ Y.
#check sq.i₂
-- Left vertical arrow Spec(K) ⟶ Spec(A).
#check sq.verticalMap
-- Right vertical is f; commutativity is sq.commSq / ValuativeCommSq.spec.
#check sq.commSq
#check AlgebraicGeometry.AlgebraicSpace.ValuativeCommSq.spec

end
