/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Finiteness.Basic

@[expose] public section

universe u

open scoped Manifold ContDiff

namespace ContMDiffMap

/-- There exists a finite flat non-projective module over the ring of smooth real functions. -/
theorem exists_finite_flat_not_projective_real :
    ∃ (M : Type u) (_ : AddCommGroup M) (_ : Module (C^∞⟮𝓘(ℝ), ℝ; ℝ⟯) M),
      Module.Finite (C^∞⟮𝓘(ℝ), ℝ; ℝ⟯) M ∧ Module.Flat (C^∞⟮𝓘(ℝ), ℝ; ℝ⟯) M ∧
        ¬ Module.Projective (C^∞⟮𝓘(ℝ), ℝ; ℝ⟯) M := sorry

end ContMDiffMap
