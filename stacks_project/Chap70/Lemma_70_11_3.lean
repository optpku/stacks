/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap70.Lemma_70_11_3_Approximation
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace
open scoped AlgebraicGeometry

universe u

/- Lemma 70.11.3: a finite morphism `f : X ⟶ Y` of algebraic spaces over a
scheme `S`, with `Y` quasi-compact and quasi-separated, presents `X` as a
directed inverse limit of algebraic spaces `X_i` over `Y` whose transition maps
are closed immersions and whose structure maps `X_i ⟶ Y` are finite and of
finite presentation. -/
@[stacks 07VR] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_finiteApproximation :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [AlgebraicSpace.IsFinite f]
      [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y],
      Nonempty (FiniteApproximation f))
