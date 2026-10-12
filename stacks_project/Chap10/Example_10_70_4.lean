/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.ReesAlgebra.Presentation.Coordinate
import StacksCheckRecall

/-!
# Example 10.70.4

The coordinate Rees algebra presentation is owned by the neutral
`ReesAlgebra.Presentation.Coordinate` API.  This chapter file is a source-facing
recall and does not duplicate the monomial straightening proof.

@stack 0G8Q
-/

@[expose] public section

/- Example 10.70.4 (Stacks tag `0G8Q`): for
`P = MvPolynomial (Fin n) R`, the Rees algebra of the variable ideal is
presented by `P[Tᵢ] / (tᵢ Tⱼ - tⱼ Tᵢ)`. -/
#check @ReesAlgebra.Presentation.relation
#check @ReesAlgebra.Presentation.relationIdeal
#check @ReesAlgebra.Presentation.toRees
#check @ReesAlgebra.Presentation.map

@[stacks 0G8Q] #check @ReesAlgebra.Presentation.Coordinate.ambient
@[stacks 0G8Q] #check @ReesAlgebra.Presentation.Coordinate.generator
@[stacks 0G8Q] #check @ReesAlgebra.Presentation.Coordinate.relationIdeal
@[stacks 0G8Q] #check @ReesAlgebra.Presentation.Coordinate.Quotient
@[stacks 0G8Q] #check @ReesAlgebra.Presentation.Coordinate.map
@[stacks 0G8Q] #check @ReesAlgebra.Presentation.Coordinate.map_surjective
@[stacks 0G8Q] #check @ReesAlgebra.Presentation.Coordinate.toRees_ker_eq_relationIdeal
@[stacks 0G8Q] #check @ReesAlgebra.Presentation.Coordinate.map_injective
@[stacks 0G8Q] #check @ReesAlgebra.Presentation.Coordinate.map_bijective
@[stacks 0G8Q] #check @ReesAlgebra.Presentation.Coordinate.equiv
@[stacks 0G8Q] #check @ReesAlgebra.Presentation.Coordinate.equiv_apply_variable
