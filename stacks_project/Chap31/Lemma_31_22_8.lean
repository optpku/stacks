/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion.Section
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 31.22.8: a section of a smooth morphism of schemes is a regular immersion. -/
@[stacks 067R] #check (@AlgebraicGeometry.Scheme.Hom.Section.isRegularImmersion :
  ∀ {X S : Scheme.{u}} {f : X ⟶ S} {σ : S ⟶ X} [AlgebraicGeometry.Smooth f],
    σ ≫ f = 𝟙 S → AlgebraicGeometry.IsRegularImmersion σ)
