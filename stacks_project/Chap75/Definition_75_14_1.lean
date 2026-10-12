/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap75.Definition_75_14_1_PerfectApproximation
import StacksCheckRecall

universe u

/- Definition 75.14.1: for a scheme `S`, an algebraic space `X` over `S`, a closed
subset `T` of `Points X`, an object `E` of `DerivedQCoh X`, and `m : ℤ`, approximation
holds for the triple `(T, E, m)` when a perfect object `P` of `D(𝒪_X)` supported on `T`
maps to `E`, inducing cohomology isomorphisms in every degree `i` with `m < i` and an
epimorphism in degree `m`. -/
@[stacks 08HI] #check
  (AlgebraicGeometry.AlgebraicSpace.HasPerfectApproximation :
    {S : AlgebraicGeometry.Scheme.{u}} →
      {X : AlgebraicGeometry.AlgebraicSpace S} →
      (T : TopologicalSpace.Closeds (AlgebraicGeometry.AlgebraicSpace.Points X)) →
      (E : AlgebraicGeometry.AlgebraicSpace.DerivedQCoh X) →
      (m : ℤ) → Prop)
