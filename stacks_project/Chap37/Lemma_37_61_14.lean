module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Perfect.Locality
import StacksCheckRecall

universe u

/- Lemma 37.61.14: perfectness of scheme morphisms is local at the source for the
fppf precoverage. -/
@[stacks 069D] #check
  (AlgebraicGeometry.LocallyOfType.isPerfectRingMap_isLocalAtSourceFppf :
    CategoryTheory.MorphismProperty.IsLocalAtSource
      (@AlgebraicGeometry.LocallyOfType.{u} RingHom.IsPerfectRingMap)
      AlgebraicGeometry.Scheme.fppfPrecoverage)
