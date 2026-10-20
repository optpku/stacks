/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RelativeCycle
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CyclesOnFibers
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Topology.LocallyConstant.Basic

@[expose] public section

open AlgebraicGeometry CategoryTheory
open Scheme.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeCycle

/-- The component coefficient function of a relative `r`-cycle on a smooth
morphism of relative dimension `r` over a locally Noetherian base is locally constant. -/
theorem isLocallyConstant_componentCoeff {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] {r : ℕ}
    [SmoothOfRelativeDimension r f] (α : CyclesOnFibers f r) (hα : IsRelative α) :
    IsLocallyConstant (CyclesOnFibers.componentCoeff f α) := sorry

/-- The geometric support of a relative `r`-cycle on a smooth morphism of relative
dimension `r` is the function support of its component coefficient function. -/
theorem support_eq_componentCoeff_support {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] {r : ℕ}
    [SmoothOfRelativeDimension r f] (α : CyclesOnFibers f r) (hα : IsRelative α) :
    CyclesOnFibers.support α = Function.support (CyclesOnFibers.componentCoeff f α) := sorry

/-- The support of a relative `r`-cycle on a smooth morphism of relative dimension
`r` over a locally Noetherian base is open and closed in the total space. -/
theorem isClopen_support {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] {r : ℕ}
    [SmoothOfRelativeDimension r f] (α : CyclesOnFibers f r) (hα : IsRelative α) :
    IsClopen (CyclesOnFibers.support α) := sorry

end AlgebraicGeometry.RelativeCycle
