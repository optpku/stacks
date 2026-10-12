/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap70.Proposition_70_8_1_Approximation
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace
open scoped AlgebraicGeometry

universe u

/- Proposition 70.8.1: a quasi-compact and quasi-separated algebraic space over
`Spec ℤ` is a directed inverse limit of quasi-separated algebraic spaces of
finite type over `ℤ` with affine transition morphisms. -/
@[stacks 07SU] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_absoluteNoetherianApproximation :
    ∀ (X : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ))))
      [IsQuasiCompact X] [IsQuasiSeparated X],
      Nonempty (AbsoluteNoetherianApproximation X))
