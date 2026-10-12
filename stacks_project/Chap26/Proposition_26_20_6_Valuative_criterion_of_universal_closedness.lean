/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ValuativeCriterion.UniversallyClosed
import StacksCheckRecall

@[expose] public section

namespace AlgebraicGeometry

/- Proposition 26.20.6 (Valuative criterion of universal closedness): for quasi-compact
morphisms, universal closedness is equivalent to existence in the valuative criterion. -/
@[stacks 01KF] #check UniversallyClosed.eq_valuativeCriterion
#check UniversallyClosed.valuativeCriterion

end AlgebraicGeometry
