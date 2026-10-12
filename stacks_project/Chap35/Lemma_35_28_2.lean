/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Locality
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 35.28.2: local finite type of scheme morphisms is local on the source for the
fppf precoverage. -/
@[stacks 036O] #check
  (AlgebraicGeometry.LocallyOfFiniteType.isLocalAtSourceFppf :
    CategoryTheory.MorphismProperty.IsLocalAtSource
      (@AlgebraicGeometry.LocallyOfFiniteType :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fppfPrecoverage)
