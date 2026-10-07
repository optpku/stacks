module

import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.Normalization
import StacksCheckRecall

open AlgebraicGeometry

universe u

/- Lemma 29.53.9: for a quasi-compact and quasi-separated morphism `f : Y ⟶ X`,
every generic point of `f.normalization` is the image under `f.toNormalization` of a
generic point of `Y`. -/
@[stacks 0AXP] #check
  (AlgebraicGeometry.Scheme.Hom.surjOn_genericPoints_toNormalization :
    ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f],
      Set.SurjOn f.toNormalization (genericPoints Y) (genericPoints f.normalization))
