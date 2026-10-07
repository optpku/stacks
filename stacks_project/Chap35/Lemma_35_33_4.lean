module

public import ReasLib.AlgebraicGeometry.Scheme.Germ.Morphism.Flat
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 35.33.4: the property that the induced map
`Y.scheme.presheaf.stalk Y.point ⟶ X.scheme.presheaf.stalk X.point` is flat is étale local
on the source-and-target for morphisms of scheme germs. -/
@[stacks 04ND] #check
  (AlgebraicGeometry.Scheme.Germ.MorphismProperty.flat_isEtaleLocal :
    AlgebraicGeometry.Scheme.Germ.MorphismProperty.IsEtaleLocal
      AlgebraicGeometry.Scheme.Germ.MorphismProperty.flat)
