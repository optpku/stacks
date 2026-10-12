/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import StacksCheckRecall

@[expose] public section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {R₁ R₂ : ComposableArrows C 4} (φ : R₁ ⟶ R₂)
variable (hR₁ : R₁.Exact) (hR₂ : R₂.Exact)
variable (h₀ : Epi (ComposableArrows.app' φ 0))
variable (h₁ : IsIso (ComposableArrows.app' φ 1))
variable (h₃ : IsIso (ComposableArrows.app' φ 3))
variable (h₄ : Mono (ComposableArrows.app' φ 4))

/- Lemma 12.5.20: the canonical five lemma for a morphism of exact five-term
sequences. -/
@[stacks 05QB] #check
  (Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono hR₁ hR₂ φ h₀ h₁ h₃ h₄ :
    IsIso (ComposableArrows.app' φ 2))

end CategoryTheory
