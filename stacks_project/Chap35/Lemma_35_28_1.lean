/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Locality
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 35.28.1: local finite presentation of scheme morphisms is local on the source
for the fppf precoverage. -/
@[stacks 036N] #check
  (AlgebraicGeometry.LocallyOfFinitePresentation.isLocalAtSourceFppf :
    CategoryTheory.MorphismProperty.IsLocalAtSource
      (@AlgebraicGeometry.LocallyOfFinitePresentation :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fppfPrecoverage)
