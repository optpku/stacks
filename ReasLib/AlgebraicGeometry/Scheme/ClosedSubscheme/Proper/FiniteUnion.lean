/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Proper
import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Proper.Mapping
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Finite.Coproduct
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Proper.Coproduct

/-!
# Finite unions of proper closed subsets

A finite union of closed subsets proper over a base scheme is proper over that base.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace ClosedSubset

/-- A finite supremum of closed subsets proper over a base scheme is proper over that base. -/
@[stacks 0CYR]
theorem IsProperOver.iSup
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    {ι : Type u} [Finite ι] (Z : ι → TopologicalSpace.Closeds X)
    (hproper : ∀ i, IsProperOver f (Z i)) :
    IsProperOver f (iSup Z) := sorry

/-- The finite supremum of an inferred family of proper closed subsets is proper. -/
instance instIsProperOverISup
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    {ι : Type u} [Finite ι] (Z : ι → TopologicalSpace.Closeds X)
    [∀ i, IsProperOver f (Z i)] :
    IsProperOver f (iSup Z) :=
  IsProperOver.iSup f Z (fun i ↦ show IsProperOver f (Z i) from inferInstance)

end ClosedSubset

end AlgebraicGeometry
