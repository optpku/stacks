/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Geometry.Manifold.Algebra.SmoothFunctions.Flat
import StacksCheckRecall

@[expose] public section

universe u

open scoped Manifold ContDiff

/- Exercise 111.5.3: the smooth-function ring supplies the requested ring, and
the theorem supplies a finite flat module that is not projective. -/
@[stacks 02CS]
#check (ContMDiffMap.exists_finite_flat_not_projective_real :
  ∃ (M : Type u) (_ : AddCommGroup M) (_ : Module (C^∞⟮𝓘(ℝ), ℝ; ℝ⟯) M),
    Module.Finite (C^∞⟮𝓘(ℝ), ℝ; ℝ⟯) M ∧ Module.Flat (C^∞⟮𝓘(ℝ), ℝ; ℝ⟯) M ∧
      ¬ Module.Projective (C^∞⟮𝓘(ℝ), ℝ; ℝ⟯) M)
