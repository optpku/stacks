module

public import ReasLib.AlgebraicGeometry.Scheme.Germ.Morphism.Gorenstein
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 76.27.1: The property of morphisms of germs of schemes that the local
ring of the fibre is Noetherian and Gorenstein is étale local on the
source-and-target. -/
@[stacks 0E13]
#check
  (AlgebraicGeometry.Scheme.Germ.MorphismProperty.fiberStalkGorenstein_isEtaleLocal :
    AlgebraicGeometry.Scheme.Germ.MorphismProperty.IsEtaleLocal
      AlgebraicGeometry.Scheme.Germ.MorphismProperty.fiberStalkGorenstein)
