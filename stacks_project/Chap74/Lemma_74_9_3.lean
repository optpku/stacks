module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian.Descent
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 74.9.3: If `f : X ⟶ Y` is a morphism of algebraic spaces that is locally
of finite presentation, flat, and surjective, and `X` is locally Noetherian, then
`Y` is locally Noetherian. -/
@[stacks 06MJ] #check
  (AlgebraicGeometry.AlgebraicSpace.IsLocallyNoetherian.of_locallyOfFinitePresentation_flat_surjective :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
      (f : X ⟶ Y) [AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation f]
      [AlgebraicGeometry.AlgebraicSpace.Flat f] [AlgebraicGeometry.AlgebraicSpace.Surjective f]
      [AlgebraicGeometry.AlgebraicSpace.IsLocallyNoetherian X],
      AlgebraicGeometry.AlgebraicSpace.IsLocallyNoetherian Y)
