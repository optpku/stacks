/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap75.Remark_75_16_4_Generation
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.AlgebraicSpace TopologicalSpace

universe u

/- Remark 75.16.4: if `X` is a quasi-compact and quasi-separated algebraic space over a
scheme `S` and `T ⊆ |X|` is closed with quasi-compact complement, then a perfect object of
`D_QCoh,T(𝒪_X)` which is a generator for `D_QCoh,T(𝒪_X)` is a classical generator for the
compact objects of `D_QCoh,T(𝒪_X)`, equivalently `D_perf,T(𝒪_X)`. Existence of such a
generator is Lemma 75.15.6. -/
@[stacks 0GFD]
#check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.SupportedOn.isClassicalGeneratorOfCompacts :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
      (T : Closeds (Points X)),
      QuasiCompact (OpenSubspace.ofOpensι T.compl) →
        ∀ (G : AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.SupportedOn X (T : Set (Points X))),
          ModuleDerived.IsPerfect G.obj →
            CategoryTheory.IsWeakGenerator G →
              CategoryTheory.IsClassicalGeneratorOfCompacts G)
