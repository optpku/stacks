/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.NormalizedSequence
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Definition 89.8.2: Let `S` be a scheme. Let `Y` be a 2-dimensional Noetherian integral
algebraic space over `S`. We say `Y` has a resolution of singularities by normalized blowups
if there exists a sequence `Y_n ⟶ ⋯ ⟶ Y_1 ⟶ Y_0 ⟶ Y` where each `Y_i` is proper over `Y`,
`Y_0 ⟶ Y` is the normalization, each `Y_i ⟶ Y_{i-1}` is a normalized blowup, and `Y_n` is
regular. -/
@[stacks 0BHX] #check (AlgebraicGeometry.AlgebraicSpace.HasResolutionByNormalizedBlowups :
  ∀ {S : Scheme.{u}} (Y : AlgebraicSpace S) [IsNoetherian Y] [IsIntegral Y],
    dimension Y = 2 → Prop)
#check (AlgebraicGeometry.AlgebraicSpace.hasResolutionByNormalizedBlowups_iff :
  ∀ {S : Scheme.{u}} (Y : AlgebraicSpace S) [IsNoetherian Y] [IsIntegral Y]
    (h_dim : dimension Y = 2),
    HasResolutionByNormalizedBlowups Y h_dim ↔
      ∃ (Z : AlgebraicSpace S) (s : NormalizedBlowupSequence Y.normalization Z),
        Proper Y.normalizationTo ∧ s.EveryTargetOver Y.normalizationTo ∧ IsRegular Z)
