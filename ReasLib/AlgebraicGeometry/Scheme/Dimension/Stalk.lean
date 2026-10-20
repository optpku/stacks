/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Properties

/-!
# Dimensions of scheme stalks

The topological Krull dimension of a scheme is recovered from the Krull dimensions of its
local rings.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- The topological Krull dimension of a scheme is the supremum of the Krull dimensions of
its local rings. -/
theorem topologicalKrullDim_eq_iSup_ringKrullDim_stalk (X : Scheme.{u}) :
    topologicalKrullDim X = ⨆ x : X, ringKrullDim (X.presheaf.stalk x) := sorry

end AlgebraicGeometry.Scheme
