/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.RelativeProj
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteComponents

/-!
# Finite irreducible components on compact opens after blowup
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Blowup

/-- A blowup in any closed subspace preserves the property that every quasi-compact
open of a surjective étale scheme atlas has finitely many irreducible components. -/
theorem hasFiniteIrreducibleComponentsOnCompactOpens
    {S : Scheme.{u}} {X : AlgebraicSpace S} (Z : ClosedSubspace X)
    (π : along Z) [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    HasFiniteIrreducibleComponentsOnCompactOpens (alongSpace Z π) := sorry

end AlgebraicGeometry.AlgebraicSpace.Blowup
