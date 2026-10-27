/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Pullback

import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

@[expose] public section

universe u

/- Lemma 60.8.3: a flat right-hand thickening map with cartesian source-inclusion
square makes a fibre square of relative crystalline objects cartesian on thickenings. -/
@[stacks 07IA] #check
  (AlgebraicGeometry.Scheme.Crystalline.Base.thickening_isPullback_of_flat :
    ∀ {p : ℕ} [Fact p.Prime] (B : Scheme.Crystalline.Base.{u} p)
      {c₁ c₂ c₃ c :
        RelativeCRIS B.scheme B.ideal B.dividedPowers B.compatible B.source B.sourceToClosed}
      (top : c₃ ⟶ c₂) (left : c₃ ⟶ c₁) (bottom : c₁ ⟶ c) (right : c₂ ⟶ c),
      IsPullback left top bottom right → ∀ [Flat right.thickening],
      IsPullback right.source.left c₂.1.inclusion c.1.inclusion right.thickening →
      IsPullback left.thickening top.thickening bottom.thickening right.thickening)
