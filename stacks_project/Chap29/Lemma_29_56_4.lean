module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.Topology
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 29.56.4: the image of a closed nowhere dense subset under a quasi-finite morphism of
schemes is nowhere dense. -/
@[stacks 03J2] #check
  (AlgebraicGeometry.Scheme.Hom.QuasiFinite.isNowhereDense_image_of_isClosed :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : Y ⟶ X)
      [AlgebraicGeometry.Scheme.Hom.QuasiFinite f] (T : Set Y),
      IsClosed T → IsNowhereDense T → IsNowhereDense (f '' T))
