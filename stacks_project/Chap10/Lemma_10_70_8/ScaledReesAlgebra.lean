/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.ReesAlgebra.Scaling
import StacksCheckRecall

/-!
# Lemma 10.70.8 Rees scaling recall

The principal Rees-algebra scaling construction is owned by
`ReesAlgebra.Scaling`.
-/

@[expose] public section

/- Lemma 10.70.8 (0BBI): recall the graded Rees-algebra scaling map. -/
@[stacks 0BBI] #check @ReesAlgebra.Scaling.gradedHom
#check @ReesAlgebra.Scaling.ideal
#check @ReesAlgebra.Scaling.element
#check @ReesAlgebra.Scaling.mem_ideal_pow_iff
#check @ReesAlgebra.Scaling.ringHom
#check @ReesAlgebra.Scaling.ringHom_monomial
#check @ReesAlgebra.Scaling.gradedHom_degreeOne
