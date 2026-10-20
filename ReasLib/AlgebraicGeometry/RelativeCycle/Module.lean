/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RelativeCycle
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedCycle.FiberFamily
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.InDimensions

/-!
# Relative cycles from dimensionally flat modules

The associated fibrewise cycle family of a quasi-coherent finite-type module
is relative when the module is flat over the base in sufficiently large dimensions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Over a locally Noetherian base, the associated fibrewise cycle family of a
quasi-coherent finite-type module with fibre support dimension at most `r` that
is flat over the base in dimensions `≥ r` is a relative `r`-cycle. -/
theorem moduleFiberCycleFamily_isRelative {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] (r : ℕ)
    (hF : f.fiberModuleSupportDimensionLE F r)
    (hflat : Modules.flatOverInDimensionsGE F f r) :
    RelativeCycle.IsRelative (moduleFiberCycleFamily f F r hF) := sorry

/-- The associated fibrewise family of a quasi-coherent finite-type module that is
flat over `S` in dimensions `≥ r` lies in the group `z(X/S, r)` of relative
`r`-cycles. -/
theorem moduleFiberCycleFamily_mem_group {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] (r : ℕ)
    (hF : f.fiberModuleSupportDimensionLE F r)
    (hflat : Modules.flatOverInDimensionsGE F f r) :
    moduleFiberCycleFamily f F r hF ∈ RelativeCycle.group f r := by
  exact moduleFiberCycleFamily_isRelative f F r hF hflat

end AlgebraicGeometry.Scheme.Hom
