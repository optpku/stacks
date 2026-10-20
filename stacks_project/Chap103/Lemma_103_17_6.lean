/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Coherent.Extensions
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory GroupoidsOver

universe u

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] [IsLocallyNoetherian X]

/- Lemma 103.17.6: let `X` be a locally Noetherian algebraic stack. Given a short
exact sequence `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` in `Mod(𝒪_X)` with `F₁` and `F₃`
coherent, then `F₂` is coherent. -/
@[stacks 0GRA]
#check (AlgebraicGeometry.AlgebraicStack.IsCoherent.middle_of_shortExact :
  ∀ {sc : ShortComplex (SheafOfModules.{u} (structureSheaf X))},
    sc.ShortExact →
      ∀ [AlgebraicStack.IsCoherent sc.X₁] [AlgebraicStack.IsCoherent sc.X₃],
        AlgebraicStack.IsCoherent sc.X₂)
