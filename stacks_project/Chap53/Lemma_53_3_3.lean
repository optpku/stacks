/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.LinearSeries
import StacksCheckRecall

@[expose] public section

open TopologicalSpace
open scoped AlgebraicGeometry

universe u

/- Lemma 53.3.3: if a proper scheme of topological dimension at most one over a field has a
linear series of degree `d` and dimension `r`, then it has one of degree `d` and dimension `s`
for every `s ≤ r`. -/
@[stacks 0CCQ] #check (AlgebraicGeometry.LinearSeries.exists_of_dimension_le :
  ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k)
    [AlgebraicGeometry.IsProper X.hom] (hdim : topologicalKrullDim X.left ≤ 1) {d r : ℕ},
    Nonempty (AlgebraicGeometry.LinearSeries X hdim d r) → ∀ (s : ℕ), s ≤ r →
      Nonempty (AlgebraicGeometry.LinearSeries X hdim d s))
