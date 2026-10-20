module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.EmbeddingDimension
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
variable (X : SchemeOverField k) [LocallyAlgebraic X]
variable (x : X.left) (hx : IsClosed {x})

/- Definition 33.46.1: over an algebraically closed field, the embedding dimension at a closed
point is the dimension over the base field of the local cotangent space `𝔪_x / 𝔪_x^2`. -/
@[stacks 0C1Q] #check
  (AlgebraicGeometry.SchemeOverField.embeddingDimensionAt_eq_cotangentDimensionAt_of_closedPoint
    X x hx :
    AlgebraicGeometry.Scheme.embeddingDimensionAt x =
      AlgebraicGeometry.SchemeOverField.cotangentDimensionAt X x)
