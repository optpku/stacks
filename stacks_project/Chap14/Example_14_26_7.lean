module

public import ReasLib.AlgebraicTopology.SimplicialSet.StdSimplex.Contractible
import StacksCheckRecall

/-!
@stack 08Q3

# Source-facing bridge for Example 14.26.7

The explicit last-vertex contraction and the resulting homotopy equivalence are owned by
`SSet.stdSimplex` in ReasLib.
-/

@[expose] public section

open CategoryTheory
open scoped Simplicial

namespace SSet.stdSimplex

variable (m : ℕ)

/- Example 14.26.7: `Δ[m]` is simplicially homotopy equivalent to the point `Δ[0]`. -/
@[stacks 08Q3]
#check (homotopyEquiv m :
  SimplicialObject.HomotopyEquiv (Δ[m] : SSet) (Δ[0] : SSet))

#check contraction m
#check contraction.homotopy m
#check contraction.endpointZero m
#check contraction.endpointOne m

end SSet.stdSimplex
