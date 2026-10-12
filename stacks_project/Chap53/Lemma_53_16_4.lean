/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.Nodal
import StacksCheckRecall

@[expose] public section

open TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.SchemeOverField

/- Lemma 53.16.4: a multicross singularity on a reduced algebraic one-dimensional
Gorenstein scheme over an algebraically closed field is an ordinary double point. -/
@[stacks 0CDZ] #check
  (AlgebraicGeometry.SchemeOverField.isOrdinaryDoublePoint_of_isMulticrossSingularity :
    ∀ {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k) [Algebraic X]
    [IsReduced X.left] (h_dimension : topologicalKrullDim X.left = 1)
    [Scheme.Gorenstein X.left] (x : X.left) (hx : isMulticrossSingularity X x),
      isOrdinaryDoublePoint X x)

end AlgebraicGeometry.SchemeOverField
