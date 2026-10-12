/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap70.Lemma_70_9_4_FinitePresentation
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder

universe u

/- Lemma 70.9.4: let `S` be a scheme. Let `X` be a quasi-compact and quasi-separated algebraic
space over `S`. Let `A` be a quasi-coherent `𝒪_X`-algebra. Then `A` is a directed colimit of
finitely presented quasi-coherent `𝒪_X`-algebras. -/
@[stacks 082A] #check
  (finitelyPresentable_ind :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsQuasiCompact X]
      [IsAbsolutelyQuasiSeparated X] (A : X.QcAlgebraUnder),
      (finitelyPresentableProperty X).ind.{u} A.obj)
