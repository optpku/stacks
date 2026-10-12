/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.SplitNode
import StacksCheckRecall

@[expose] public section

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.SchemeOverField

/- Definition 53.19.10: a split node is the promoted scheme-level split-node predicate. -/
@[stacks 0CBV] #check
  (AlgebraicGeometry.SchemeOverField.isSplitNode :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [Algebraic X]
      (h_dimension : topologicalKrullDim X.left = 1) (x : X.left), Prop)

end AlgebraicGeometry.SchemeOverField
