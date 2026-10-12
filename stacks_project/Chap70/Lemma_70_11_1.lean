/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap70.Lemma_70_11_1_Approximation
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace
open scoped AlgebraicGeometry

universe u

/- Lemma 70.11.1: an affine morphism `f : X ⟶ Y` of algebraic spaces over a
scheme `S`, with `Y` quasi-compact and quasi-separated, presents `X` as a
directed inverse limit of algebraic spaces `X_i` over `Y` whose transition maps
are affine and whose structure maps `X_i ⟶ Y` are affine of finite
presentation. -/
@[stacks 0870] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_affineApproximation :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [AlgebraicSpace.Affine f]
      [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y],
      Nonempty (AffineApproximation f))
