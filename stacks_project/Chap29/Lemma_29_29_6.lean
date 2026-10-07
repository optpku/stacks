module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFormula
import StacksCheckRecall

open AlgebraicGeometry

universe u

/- Lemma 29.29.6: Let `f : X ⟶ Y` be a flat morphism of locally Noetherian schemes of
relative dimension `d`. For every `x : X`, the local dimension at `x` equals the local dimension
at `f x` plus `d`. -/
@[stacks 0AFE] #check
  (AlgebraicGeometry.Scheme.Hom.DimensionFormula.topologicalKrullDimAt_eq_image_add_relativeDimension_of_flat :
    ∀ {X Y : Scheme.{u}} {d : ℕ} (f : X ⟶ Y) [IsLocallyNoetherian X]
      [IsLocallyNoetherian Y] [Flat f] [Scheme.Hom.RelativeDimension f d] (x : X),
      topologicalKrullDimAt x = topologicalKrullDimAt (f x) + (d : WithBot ℕ∞))
