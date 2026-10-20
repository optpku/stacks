module

public import stacks_project.Chap48.Definition_48_2_2_DualizingComplex
import StacksCheckRecall

universe u

/- Definition 48.2.2: for a locally Noetherian scheme `X`, a complex `K` in `D(𝒪_X)`
is dualizing when it satisfies the equivalent affine-local conditions of Lemma 48.2.1. -/
@[stacks 0A87] #check (AlgebraicGeometry.Scheme.IsDualizingComplex :
  {X : AlgebraicGeometry.Scheme.{u}} →
    [AlgebraicGeometry.IsLocallyNoetherian X] →
      AlgebraicGeometry.RingedSpace.ModuleDerived X.toRingedSpace → Prop)
