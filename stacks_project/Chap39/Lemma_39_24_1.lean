/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.AffineOpen
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 39.24.1: For a groupoid scheme with finite locally free source and target maps,
an orbit contained in an affine open has an invariant affine open neighbourhood. -/
@[stacks 03JE] #check
  (AlgebraicGeometry.GroupoidScheme.exists_invariantAffineOpen :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S)
      [AlgebraicGeometry.IsFiniteLocallyFree G.s.left]
      [AlgebraicGeometry.IsFiniteLocallyFree G.t.left]
      (u : G.U.left) (W : G.U.left.affineOpens),
      G.t.left '' (G.s.left ⁻¹' {u}) ⊆ (W : Set G.U.left) →
        ∃ V : G.U.left.affineOpens,
          u ∈ (V : G.U.left.Opens) ∧
            G.toPreRelation.IsOpenInvariant (V : G.U.left.Opens))
