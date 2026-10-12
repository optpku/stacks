/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension.FiniteType

@[expose] public section

namespace AlgebraicGeometry

universe u

namespace Scheme.Hom

/- Lemma 29.28.4: for a locally finite type morphism, the locus where the local fibre dimension
is at most `n` is open. -/
@[stacks 02FZ] #check
  (AlgebraicGeometry.Scheme.Hom.isOpen_fiberDimensionLELocus :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (n : ℕ),
      IsOpen (f.fiberDimensionLELocus n))

end Scheme.Hom

end AlgebraicGeometry
