/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap92.«92_28_0_1_FibreProduct»
import StacksCheckRecall

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Cotangent
open AlgebraicGeometry.AlgebraicSpace.Cotangent.FibreProduct

universe u

variable {S : Scheme.{u}}
variable {B X Y : AlgebraicSpace S}
variable (f : X ⟶ B) (g : Y ⟶ B)

/- 92.28.0.1: for morphisms X ⟶ B and Y ⟶ B of algebraic spaces over a scheme S,
with W = X ×_B Y and projections p, q, the fibre-product diagram of cotangent
complexes in D(O_W) has middle row the transitivity triangle of W ⟶ X ⟶ B,
middle column the transitivity triangle of W ⟶ Y ⟶ B, identity equalities on
Lp^* L_{X/B} and Lq^* L_{Y/B}, and a new object E = cone f g filling the
upper-right corner so that the top row Lp^* L_{X/B} ⟶ L_{W/Y} ⟶ E and the
right column Lq^* L_{Y/B} ⟶ L_{W/X} ⟶ E are distinguished. E is the mapping
cone of the sum of the two transitivity maps into L_{W/B}. -/
@[stacks 09DK]
#check cone f g

#check sumMap f g
#check coneInr f g
#check topMap f g
#check rightMap f g
#check fromOverY f g
#check fromOverX f g
#check toConeFromOverX f g
#check toConeFromOverY f g
#check transitivityTriangle (pullback.fst f g) f
#check transitivityTriangle (pullback.snd f g) g
