/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Support
import StacksCheckRecall

open AlgebraicGeometry

universe u

section

variable (X : Scheme.{u})

/- Definition 42.8.3: For an integral algebraic cycle, the support is the union of the
closures `{x}` representing components with nonzero coefficient. -/
@[stacks 0H46] #check
  (AlgebraicGeometry.AlgebraicCycle.geometricSupport : AlgebraicCycle X ℤ → Set X)

#check @AlgebraicCycle.geometricSupport_def
#check @AlgebraicCycle.mem_geometricSupport
#check @AlgebraicCycle.isClosed_geometricSupport

end
