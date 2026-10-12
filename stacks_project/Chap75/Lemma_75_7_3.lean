/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubset.Proper
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 75.7.3: if `T' ≤ T` are closed subsets of `|X|` and `T` is proper
over `Y` along a locally of finite type morphism of algebraic spaces, then
`T'` is proper over `Y`. -/
@[stacks 0CZE] #check
  (AlgebraicGeometry.AlgebraicSpace.ClosedSubset.ProperOver.mono :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
      {f : X ⟶ Y} [AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType f]
      {T' T : TopologicalSpace.Closeds (AlgebraicGeometry.AlgebraicSpace.Points X)},
      T' ≤ T → AlgebraicGeometry.AlgebraicSpace.ClosedSubset.ProperOver f T →
        AlgebraicGeometry.AlgebraicSpace.ClosedSubset.ProperOver f T')
