/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.GeometricallyReduced
import Mathlib.Tactic.CrossRefAttribute
import ReasLib.AlgebraicGeometry.Scheme.Limit.FinitePresentation
import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.GeometricallyReducedFiber
import ReasLib.AlgebraicGeometry.Scheme.Topology.Constructible
import ReasLib.Topology.Constructible.Irreducible

/-!
# Constructibility of geometrically reduced fibre loci

This module records local constructibility of the locus where the geometric fibres of a
quasi-compact, locally finitely presented scheme morphism are reduced.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The geometrically reduced fibre locus of a quasi-compact scheme morphism locally of finite
presentation is locally constructible in the target. -/
@[stacks 0579]
theorem isLocallyConstructible_geometricallyReducedFiberLocus
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [LocallyOfFinitePresentation f] :
    Topology.IsLocallyConstructible f.geometricallyReducedFiberLocus := sorry

end AlgebraicGeometry.Scheme.Hom
