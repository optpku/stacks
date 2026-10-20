/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.Algebra.Module.Graded.Quotient.RestrictScalars
public import ReasLib.LinearAlgebra.Quotient.Intersection

/-!
# Restricted quotient intersections in graded applications

For a graded family `𝒜`, the intersection and kernel attached to degree `i` are the specialization
of the general `Submodule.Quotient` API at `p := 𝒜 i`.  This file is a discoverability
facade only: it introduces no family-specific wrapper declarations and requires no `DecidableEq` or
decomposition instance.
-/

@[expose] public section
