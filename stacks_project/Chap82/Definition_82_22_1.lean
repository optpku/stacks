module

public import stacks_project.Chap82.Definition_82_22_1_Chow
public import stacks_project.Chap82.Definition_82_22_1_Gysin
public import stacks_project.Chap82.Definition_82_22_1_Intersection
import StacksCheckRecall

/-!
# Definition 82.22.1

The refined Gysin homomorphism associated to a global section of an invertible
module on a good algebraic space, and Cartier intersection when the zero scheme
is an effective Cartier divisor.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

/- Definition 82.22.1 (1): In Situation 82.2.1, for good `X / B`, an invertible
sheaf `L` and a global section `s`, with `D = Z(s)` and `i : D ⟶ X` the closed
immersion, the refined Gysin homomorphism
`i* : Z_{k+1}(X) ⟶ CH_k(D)` is `Hom.gysin f δ L s k`. On an integral closed
subspace `W ⊂ X` of `δ`-dimension `k + 1` it is `[D ∩ W]_k` if `W ⊄ D`, and
`i'_*(c1(L|_W) ∩ [W])` if `W ⊂ D`, extended linearly to general
`(k + 1)`-cycles. -/
@[stacks 0ER1] #check Hom.gysin

/- Definition 82.22.1 (2): If `D` is an effective Cartier divisor, then
`D · α = i_* i* α` is `Hom.cartierIntersection f δ L s k`, the pushforward of
the Gysin class to a class on `X`. -/
@[stacks 0ER1] #check Hom.cartierIntersection
