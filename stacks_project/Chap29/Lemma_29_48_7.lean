module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.Finite.Topology
import StacksCheckRecall

open CategoryTheory

universe u

variable {X Y : AlgebraicGeometry.Scheme.{u}}
variable (f : Y ⟶ X) [AlgebraicGeometry.IsFinite f]
variable (T : Set Y) (hT_closed : IsClosed T) (hT_nowhere : IsNowhereDense T)

/- Lemma 29.48.7 (1): the image of `T` under `f` is closed. -/
@[stacks 03HX] #check
  (AlgebraicGeometry.Scheme.Hom.isClosedMap f T hT_closed : IsClosed (f '' T))

/- Lemma 29.48.7 (2): the image of `T` under `f` is nowhere dense. -/
@[stacks 03HX] #check
  (AlgebraicGeometry.IsFinite.isNowhereDense_image_of_isClosed
    f T hT_closed hT_nowhere : IsNowhereDense (f '' T))
