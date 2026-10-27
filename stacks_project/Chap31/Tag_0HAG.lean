/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Rank.Generic
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry.Scheme.Modules
open scoped AlgebraicGeometry
noncomputable section
universe u
variable {X : Scheme.{u}} [IsIntegral X]

/- Lemma (0HAG). Generic rank r is equivalent to section-module rank r on
every nonempty affine open, and to that condition on some nonempty affine open. -/
@[stacks 0HAG] #check
  (AlgebraicGeometry.Scheme.Modules.genericRank_affine_tfae :
    ∀ (F : X.Modules) [F.IsQuasicoherent] (r : Cardinal.{u}),
    List.TFAE [
      genericRank F = r,
      ∀ U : X.affineOpens, Nonempty (U : X.Opens) →
        Module.rank Γ(X, U) Γ(F, U) = r,
      ∃ U : X.affineOpens, Nonempty (U : X.Opens) ∧
        Module.rank Γ(X, U) Γ(F, U) = r
    ])
