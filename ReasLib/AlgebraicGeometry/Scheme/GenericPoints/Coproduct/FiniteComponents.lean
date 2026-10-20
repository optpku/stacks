/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.FiniteComponents
public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.Normalization
import Mathlib.Tactic.CrossRefAttribute

/-!
# Normalization from finite generic components

This leaf supplies the generic-point normalization prerequisites implied by
finite irreducible components on compact opens.  It is deliberately separate
from consequences about normalization fibers.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.GenericPointCoproduct.FiniteComponents

/-- Finite irreducible components on compact opens make the generic-point
residue-field coproduct map quasi-compact. -/
@[stacks 035P]
instance genericPointsQuasiCompact (X : Scheme.{u})
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X] :
    QuasiCompact (genericPointSpectrumCoproductTo X) := sorry

/-- Finite irreducible components on compact opens make the generic-point
residue-field coproduct map quasi-separated. -/
@[stacks 035P]
instance genericPointsQuasiSeparated (X : Scheme.{u})
    [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X] :
    QuasiSeparated (genericPointSpectrumCoproductTo X) := sorry

end AlgebraicGeometry.GenericPointCoproduct.FiniteComponents
