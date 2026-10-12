/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Dimension
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 29.34.21: for a smooth morphism of locally Noetherian schemes, the local dimension at a
source point is the local dimension at its image plus the local dimension of the fiber. -/
@[stacks 0AFF] #check (AlgebraicGeometry.Smooth.topologicalKrullDimAt_eq_image_add_fiberDimensionAt :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ Y}
      [AlgebraicGeometry.IsLocallyNoetherian X] [AlgebraicGeometry.IsLocallyNoetherian Y],
      AlgebraicGeometry.Smooth f → ∀ x : X,
        topologicalKrullDimAt x = topologicalKrullDimAt (f x) + f.fiberDimensionAt x)
