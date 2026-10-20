module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Generation
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
