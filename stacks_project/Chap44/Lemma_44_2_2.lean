/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Hilbert.Limit
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 44.2.2: if `X ⟶ S` is of finite presentation, then the degree-`d`
Hilbert functor `AlgebraicGeometry.Hilbert.functor X d` preserves directed affine
limits over `S`. -/
@[stacks 0B96] #check
  (AlgebraicGeometry.Hilbert.functor_preservesDirectedAffineLimits :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : Over S) (d : ℕ)
      [AlgebraicGeometry.Scheme.Hom.FinitePresentation X.hom],
      AlgebraicGeometry.Scheme.Over.PreservesDirectedAffineLimits S
        (AlgebraicGeometry.Hilbert.functor X d))
