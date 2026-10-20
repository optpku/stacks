module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.PseudoCoherent.Locality
import StacksCheckRecall

universe u

/- Lemma 37.60.13: pseudo-coherence of scheme morphisms is local at the source for the
fppf precoverage. -/
@[stacks 0699] #check
  (AlgebraicGeometry.PseudoCoherent.isLocalAtSourceFppf :
    CategoryTheory.MorphismProperty.IsLocalAtSource
      (@AlgebraicGeometry.PseudoCoherent :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fppfPrecoverage)
