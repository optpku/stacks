/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.Generator

/-!
# Compatibility Import for the Regular DG Derived Generator

The regular object and all of its generator properties are owned by
`DifferentialGradedModule.Derived.Generator`.  This file remains as a compatibility import for
clients of the earlier Morita-specific path; new foundational clients should import the owner
directly.
-/

@[expose] public section
