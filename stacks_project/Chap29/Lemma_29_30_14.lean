module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.FiberDimension
import StacksCheckRecall

open AlgebraicGeometry

universe u

/- Lemma 29.30.14: Let `f : X ⟶ S` be a syntomic morphism. The function
`x ↦ f.fiberDimensionAt x` is locally constant on `X`. -/
@[stacks 02K1] #check
  (AlgebraicGeometry.Syntomic.isLocallyConstant_fiberDimensionAt :
    ∀ {X S : Scheme.{u}} {f : X ⟶ S},
      Syntomic f → IsLocallyConstant (fun x : X ↦ f.fiberDimensionAt x))
