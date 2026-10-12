/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CohenMacaulay.Dimension
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/- Lemma 37.22.3: for a locally finite-type Cohen--Macaulay morphism of locally
Noetherian schemes, the local dimension at a source point is the local dimension at
its image plus the local dimension of the corresponding fiber. -/
@[stacks 0AFG] #check
  (AlgebraicGeometry.CohenMacaulay.topologicalKrullDimAt_eq_image_add_fiberDimensionAt :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsLocallyNoetherian X]
      [IsLocallyNoetherian Y] [LocallyOfFiniteType f] [CohenMacaulay f] (x : X),
      topologicalKrullDimAt x = topologicalKrullDimAt (f x) + f.fiberDimensionAt x)

end AlgebraicGeometry
