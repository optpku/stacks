/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap70.Lemma_70_10_2_Approximation
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace
open scoped AlgebraicGeometry

universe u

/- Lemma 70.10.2: a morphism of algebraic spaces over a scheme `S`, with
quasi-compact quasi-separated source and quasi-separated target, is a directed
inverse limit of algebraic spaces of finite presentation over the target with
affine transition morphisms over the target. -/
@[stacks 09NS] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_relativeFinitePresentationApproximation :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [IsQuasiCompact X] [IsQuasiSeparated X]
      [IsQuasiSeparated Y],
      Nonempty (RelativeFinitePresentationApproximation f))
