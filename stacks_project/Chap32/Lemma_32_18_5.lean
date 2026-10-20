/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Limit.ClosedSubscheme
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 32.18.5: let `S` be a quasi-compact and quasi-separated scheme, let
`f : X ⟶ S` be a morphism of finite presentation, and let `d ≥ 0`. If `Z ⊆ X` is a closed
subscheme whose fibres over `S` have dimension at most `d`, then there exists a closed subscheme
`Z' ⊆ X` containing `Z`, such that `Z' ⟶ X` is of finite presentation and all fibres of `Z'`
over `S` have dimension at most `d`. -/
@[stacks 05M6] #check
  (AlgebraicGeometry.Scheme.Limit.ClosedSubscheme.existsFinitePresentationContainingOfFiberDimensionLE :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}}
      [CompactSpace S.carrier] [QuasiSeparatedSpace S.carrier]
      (f : X ⟶ S) [AlgebraicGeometry.Scheme.Hom.FinitePresentation f]
      (d : ℕ) (Z : X.IdealSheafData),
      (∀ z : Z.subscheme,
        (Z.subschemeι ≫ f).fiberDimensionAt z ≤ (d : WithBot ℕ∞)) →
      ∃ Z' : X.IdealSheafData,
        ∃ _ : Z' ≤ Z, AlgebraicGeometry.Scheme.Hom.FinitePresentation Z'.subschemeι ∧
          ∀ z : Z'.subscheme,
            (Z'.subschemeι ≫ f).fiberDimensionAt z ≤ (d : WithBot ℕ∞))
