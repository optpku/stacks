/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Weighting.Constructible
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 37.76.2: every integer level set of the fibre integral of a weighting of a
locally quasi-finite morphism of finite presentation is locally constructible in the target. -/
@[stacks 0F3H] #check
  (AlgebraicGeometry.Scheme.Hom.IsWeighting.fiberIntegral_levelSet_isLocallyConstructible :
    ∀ {X Y : Scheme.{u}} {f : X ⟶ Y} [AlgebraicGeometry.LocallyQuasiFinite f]
      [Scheme.Hom.FinitePresentation f] {w : X → ℤ}, f.IsWeighting w → ∀ n : ℤ,
      Topology.IsLocallyConstructible
        {y : Y | f.fiberIntegral ⟨f.tendsto_cofinite_cofinite⟩ w y = n})
