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
