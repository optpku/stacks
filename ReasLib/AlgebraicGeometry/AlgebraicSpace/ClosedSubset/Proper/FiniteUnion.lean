/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubset.Proper

/-!
# Finite unions of closed subsets proper over a base

A finite union of closed subsets of an algebraic space that are proper over a
base remains proper over that base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u v

namespace AlgebraicGeometry.AlgebraicSpace.ClosedSubset

/-- A finite supremum of closed subsets proper over the target of a locally of
finite type morphism of algebraic spaces is proper over that target. -/
theorem ProperOver.iSup {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] {ι : Type v} [Finite ι] (T : ι → Closeds (Points X))
    (hproper : ∀ i, ProperOver f (T i)) :
    ProperOver f (iSup T) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ClosedSubset
