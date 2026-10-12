/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.OverField.Smooth.ClosedPoints
import StacksCheckRecall

universe u

/- Lemma 33.25.6: if `X` is smooth over `Spec(k)`, then the set of closed points `x ∈ X` whose
residue field extension `κ(x) / k` is finite separable is dense in `X`. -/
@[stacks 056U] #check
  (AlgebraicGeometry.SchemeOverField.dense_closedPoints_finiteSeparableResidueField_of_smooth :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
      [AlgebraicGeometry.Smooth X.hom],
      Dense ({x : X.left | x ∈ closedPoints X.left ∧
        FiniteDimensional k (X.left.residueField x) ∧
          Algebra.IsSeparable k (X.left.residueField x)} : Set X.left))
