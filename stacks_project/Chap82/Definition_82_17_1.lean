module

public import stacks_project.Chap82.Definition_82_17_1_Cycle
public import stacks_project.Chap82.Definition_82_17_1_Chow
import StacksCheckRecall

/-!
# Definition 82.17.1

The `(n-1)`-cycle of a nonzero meromorphic section of an invertible module on
a good integral algebraic space, and the class `c1(L) ∩ [X]` in `CH_{n-1}(X)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

/- Definition 82.17.1 (1): In Situation 82.2.1, for good integral `X / B` with
`n = dim_δ(X)` and an invertible `𝒪_X`-module `L`, any nonzero meromorphic
section `s` of `L` determines the `(n-1)`-cycle
`div_L(s) = Hom.meromorphicSectionDivisorCycle f δ s hs`, equal to the Weil
divisor of Spaces over Fields, Definition 72.7.4, viewed as an `(n-1)`-cycle by
Lemma 82.12.1. -/
@[stacks 0EQE]
#check Hom.meromorphicSectionDivisorCycle

/- Definition 82.17.1 (2): In Situation 82.2.1, for good integral `X / B` with
`n = dim_δ(X)` and an invertible `𝒪_X`-module `L`, the Weil divisor associated
to `L` is `c1(L) ∩ [X] = Hom.firstChernCapFundamental f δ L`, the class of
`div_L(s)` in `CH_{n-1}(X)` for any nonzero meromorphic section `s` of `L`,
well-defined by Spaces over Fields, Lemma 72.7.3. -/
@[stacks 0EQE]
#check Hom.firstChernCapFundamental
