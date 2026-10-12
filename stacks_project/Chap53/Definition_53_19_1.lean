/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.Nodal
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Definition 53.19.1: Let `k` be a field. Let `X` be a 1-dimensional locally algebraic
`k`-scheme. A closed point is a node when it has an ordinary double point above it after
base change to `AlgebraicClosure k`; `X` is at-worst-nodal when every closed point is smooth
over `k` or is a node. -/
@[stacks 0C47] #check
  (AlgebraicGeometry.SchemeOverField.isNode :
    ∀ {k : Type u} [Field k]
      (X : AlgebraicGeometry.SchemeOverField k) (x : X.left), Prop)

#check
  (AlgebraicGeometry.SchemeOverField.atWorstNodal :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k), Prop)
