module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.LocalAtSource
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 35.29.1: syntomicity of scheme morphisms is local on the source for the
syntomic precoverage. -/
@[stacks 036S] #check
  (AlgebraicGeometry.Syntomic.isLocalAtSourceSyntomic :
    CategoryTheory.MorphismProperty.IsLocalAtSource
      (@AlgebraicGeometry.Syntomic :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.bigSyntomicPrecoverage)
