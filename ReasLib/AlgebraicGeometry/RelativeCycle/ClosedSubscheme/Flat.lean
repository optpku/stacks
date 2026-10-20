/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Flat.InDimensions
public import ReasLib.AlgebraicGeometry.RelativeCycle
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberCycleFamily.ClosedSubscheme

/-!
# Relative cycles from dimensionally flat closed subschemes

The associated fibrewise cycle family of a closed subscheme is relative when
the closed subscheme is flat over the base in sufficiently large dimensions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Over a locally Noetherian base, the associated fibrewise cycle family of a
closed subscheme of fibre dimension at most `r` that is flat over the base in
dimensions `≥ r` is a relative `r`-cycle. -/
theorem closedSubschemeFiberCycleFamily_isRelative {X S : Scheme.{u}}
    (f : X ⟶ S) [IsLocallyNoetherian S] [LocallyOfFiniteType f]
    (Z : X.IdealSheafData) (r : ℕ)
    (hZ : f.fiberClosedSubschemeDimensionLE Z r)
    (hflat : f.closedSubschemeFlatOverInDimensionsGE Z r) :
    RelativeCycle.IsRelative (closedSubschemeFiberCycleFamily f Z r hZ) := sorry

/-- The associated fibrewise family of a closed subscheme that is flat over `S`
in dimensions `≥ r` lies in the group `z(X/S, r)` of relative `r`-cycles. -/
theorem closedSubschemeFiberCycleFamily_mem_group {X S : Scheme.{u}}
    (f : X ⟶ S) [IsLocallyNoetherian S] [LocallyOfFiniteType f]
    (Z : X.IdealSheafData) (r : ℕ)
    (hZ : f.fiberClosedSubschemeDimensionLE Z r)
    (hflat : f.closedSubschemeFlatOverInDimensionsGE Z r) :
    closedSubschemeFiberCycleFamily f Z r hZ ∈ RelativeCycle.group f r := by
  exact closedSubschemeFiberCycleFamily_isRelative f Z r hZ hflat

end AlgebraicGeometry.Scheme.Hom
