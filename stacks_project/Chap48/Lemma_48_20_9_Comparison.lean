/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.NewUpperShriek.Proper

@[expose] public section
open AlgebraicGeometry CategoryTheory
open scoped DerivedCategory.CohomologyIn

/-! Public compatibility surface for proper and separated comparison constructions. -/
#check AlgebraicGeometry.Scheme.NewUpperShriekAssignment.properRestriction
#check AlgebraicGeometry.Scheme.NewUpperShriekAssignment.properRestriction_isIsomorphic
#check AlgebraicGeometry.Scheme.NewUpperShriekAssignment.properTraceMap
#check AlgebraicGeometry.Scheme.NewUpperShriekAssignment.properTraceMap_isIso
#check AlgebraicGeometry.Scheme.NewUpperShriekAssignment.dualizingTrace_isIsomorphic
#check AlgebraicGeometry.Scheme.NewUpperShriekAssignment.omega_isIsomorphic_upperShriek
#check AlgebraicGeometry.Scheme.NewUpperShriekAssignment.map_obj_isIsomorphic_upperShriek
