/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import StacksCheckRecall

@[expose] public section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {R₁ R₂ : ComposableArrows C 3} (φ : R₁ ⟶ R₂)

section Epi

variable (hR₁ : R₁.Exact) (hR₂ : R₂.Exact)
variable (h₀ : Epi (ComposableArrows.app' φ 0))
variable (h₂ : Epi (ComposableArrows.app' φ 2))
variable (h₃ : Mono (ComposableArrows.app' φ 3))

/- Lemma 12.5.19 (1): the epimorphism form of the four lemma. -/
@[stacks 05QA] #check
  (Abelian.epi_of_epi_of_epi_of_mono φ hR₁ hR₂ h₀ h₂ h₃ :
    Epi (ComposableArrows.app' φ 1))

end Epi

section Mono

variable (hR₁ : R₁.Exact) (hR₂ : R₂.Exact)
variable (h₀ : Epi (ComposableArrows.app' φ 0))
variable (h₁ : Mono (ComposableArrows.app' φ 1))
variable (h₃ : Mono (ComposableArrows.app' φ 3))

/- Lemma 12.5.19 (2): the monomorphism form of the four lemma. -/
#check
  (Abelian.mono_of_epi_of_mono_of_mono φ hR₁ hR₂ h₀ h₁ h₃ :
    Mono (ComposableArrows.app' φ 2))

end Mono

end CategoryTheory
