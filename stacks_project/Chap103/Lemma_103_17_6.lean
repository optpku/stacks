/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap103.Lemma_103_17_6_Coherent
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory GroupoidsOver

universe u

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] [IsLocallyNoetherian X]

/- Lemma 103.17.6: let `X` be a locally Noetherian algebraic stack. Given a short
exact sequence `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` in `Mod(𝒪_X)` with `F₁` and `F₃`
coherent, then `F₂` is coherent. -/
@[stacks 0GRA]
#check (IsCoherent.middle_of_shortExact :
  ∀ {sc : ShortComplex (SheafOfModules.{u} (structureSheaf X))},
    sc.ShortExact →
      ∀ [AlgebraicStack.IsCoherent sc.X₁] [AlgebraicStack.IsCoherent sc.X₃],
        AlgebraicStack.IsCoherent sc.X₂)
