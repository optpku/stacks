/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension.Operations
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

/-!
# Lemma 29.29.2

Base-change stability for relative dimensions is maintained in
`ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension.Operations`.
-/

/- Lemma 29.29.2 (1): fixed relative dimension is preserved by arbitrary base change. -/
@[stacks 02NK] #check
  (AlgebraicGeometry.Scheme.Hom.relativeDimension_baseChange :
    ∀ {X S S' : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) {d : ℕ}
      [AlgebraicGeometry.Scheme.Hom.RelativeDimension f d],
      AlgebraicGeometry.Scheme.Hom.RelativeDimension (pullback.snd f g) d)

/- Lemma 29.29.2 (2): relative dimension at most `d` is preserved by arbitrary base change. -/
@[stacks 02NK] #check
  (AlgebraicGeometry.Scheme.Hom.relativeDimensionLE_baseChange :
    ∀ {X S S' : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) {d : ℕ}
      [AlgebraicGeometry.Scheme.Hom.RelativeDimensionLE f d],
      AlgebraicGeometry.Scheme.Hom.RelativeDimensionLE (pullback.snd f g) d)
