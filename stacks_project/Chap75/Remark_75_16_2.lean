/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap75.Remark_75_16_2_Generation
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Remark 75.16.2: if `X` is a quasi-compact and quasi-separated algebraic space over a
scheme `S`, then a perfect object of `D(𝒪_X)` which is a generator for `D_QCoh(𝒪_X)` is a
classical generator for the compact objects of `D_QCoh(𝒪_X)`, equivalently `D_perf(𝒪_X)`.
Existence of such a generator is Theorem 75.15.4. -/
@[stacks 0GFC]
#check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.isClassicalGeneratorOfCompacts :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
      (G : AlgebraicGeometry.AlgebraicSpace.DerivedQCoh X),
      ModuleDerived.IsPerfect G.obj →
        CategoryTheory.IsWeakGenerator G →
          CategoryTheory.IsClassicalGeneratorOfCompacts G)
