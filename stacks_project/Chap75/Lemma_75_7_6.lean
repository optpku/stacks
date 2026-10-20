/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubset.Proper.FiniteUnion
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

/- Lemma 75.7.6

For a locally finite type morphism of algebraic spaces, a finite union of closed
subsets proper over the base is proper over the base.
-/
@[stacks 0CZH] #check
  (AlgebraicGeometry.AlgebraicSpace.ClosedSubset.ProperOver.iSup :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
      (f : X ⟶ Y) [AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType f]
      {ι : Type v} [Finite ι]
      (T : ι → TopologicalSpace.Closeds (AlgebraicGeometry.AlgebraicSpace.Points X)),
      (∀ i, AlgebraicGeometry.AlgebraicSpace.ClosedSubset.ProperOver f (T i)) →
        AlgebraicGeometry.AlgebraicSpace.ClosedSubset.ProperOver f (iSup T))
