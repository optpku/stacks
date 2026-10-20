/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.VectorSpace.ProjectiveEndomorphism.Action
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.ProjectiveSpace.VectorSpace
open scoped AlgebraicGeometry

universe u

/- 43.23.7.1: for `P = scheme k (Module.Dual k (Module.End k V))`, the universal evaluation `ψ`
induces a scheme morphism `rψ : U(ψ) ⟶ P × ℙ(V)`. -/
@[stacks 0B2W] #check
  (AlgebraicGeometry.ProjectiveSpace.VectorSpace.ProjectiveEndomorphism.action :
    ∀ (k : Type u) [Field k] (V : Type u) [AddCommGroup V] [Module k V]
      (L : (ProjectiveEndomorphism.ambientScheme k V).Modules)
      [Scheme.Modules.Invertible L]
      (evaluation : grading k V →+*ᵍ RingedSpace.GradedSections.grading L)
      (P : ProjTwistPresentation (grading k V))
      (c : Scheme.Modules.ProjSectionMap (grading k V) L P evaluation)
      (hcanonical : c.IsCanonical),
      (ProjectiveEndomorphism.actionDomain k V L evaluation).toScheme ⟶
        ProjectiveEndomorphism.ambientScheme k V)
