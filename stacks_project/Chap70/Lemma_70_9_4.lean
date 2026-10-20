module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Algebra.FinitePresentation
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
  (AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder.finitelyPresentable_ind :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsQuasiCompact X]
      [IsAbsolutelyQuasiSeparated X] (A : X.QcAlgebraUnder),
      (finitelyPresentableProperty X).ind.{u} A.obj)
