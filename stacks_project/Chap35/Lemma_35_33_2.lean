module

public import ReasLib.AlgebraicGeometry.Scheme.Germ.Morphism.RepresentedBy
import StacksCheckRecall

universe u

/- Lemma 35.33.2: if `P` is étale local on source-and-target for scheme morphisms,
then having a representative satisfying `P` is étale local on source-and-target for germ
morphisms. -/
@[stacks 04R6] #check
  (AlgebraicGeometry.Scheme.Germ.MorphismProperty.representedBy_isEtaleLocal :
    (P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u}) →
      [AlgebraicGeometry.IsEtaleLocalAtSourceAndTarget P] →
        AlgebraicGeometry.Scheme.Germ.MorphismProperty.IsEtaleLocal
          (AlgebraicGeometry.Scheme.Germ.MorphismProperty.representedBy P))
