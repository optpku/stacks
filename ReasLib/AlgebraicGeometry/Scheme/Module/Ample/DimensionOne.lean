/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.ClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.GloballyGenerated
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.OpenComplement
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.ClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Reduction
public import ReasLib.AlgebraicGeometry.Scheme.Reduction.UniversalHomeomorphism

/-!
# Ample invertible modules on one-dimensional schemes

This file records existence results for ample invertible modules on Noetherian separated schemes
of topological Krull dimension one.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Every Noetherian integral separated scheme of topological Krull dimension one has an ample
invertible module. -/
@[stacks 09ND]
theorem hasAmpleInvertibleModule_of_dimension_one
    {X : Scheme.{u}} [IsNoetherian X] [IsIntegral X] [X.IsSeparated]
    (hdim : topologicalKrullDim X = 1) :
    HasAmpleInvertibleModule X := sorry

/-- Every Noetherian reduced separated scheme of topological Krull dimension one has an ample
invertible module. -/
@[stacks 09NX]
theorem hasAmpleInvertibleModule_of_reduced_dimension_one
    {X : Scheme.{u}} [IsNoetherian X] [IsReduced X] [X.IsSeparated]
    (hdim : topologicalKrullDim X = 1) :
    HasAmpleInvertibleModule X := sorry

/-- Every Noetherian separated scheme of topological Krull dimension one has an ample invertible
module. -/
@[stacks 09NZ]
theorem hasAmpleInvertibleModule_of_noetherian_separated_dimension_one
    {X : Scheme.{u}} [IsNoetherian X] [X.IsSeparated]
    (hdim : topologicalKrullDim X = 1) :
    HasAmpleInvertibleModule X := sorry

/-- If the reduction of a scheme is Noetherian, separated, and has topological Krull dimension
one, then the scheme has an ample invertible module. -/
@[stacks 09P0]
theorem hasAmpleInvertibleModule_of_reduction_dimension_one
    {X : Scheme.{u}} [IsNoetherian X.reduction] [X.reduction.IsSeparated]
    (hdim : topologicalKrullDim X.reduction = 1) :
    HasAmpleInvertibleModule X := sorry

end AlgebraicGeometry.Scheme.Modules
