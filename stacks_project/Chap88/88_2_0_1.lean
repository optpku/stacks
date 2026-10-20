/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicAlgebraSystem
import StacksCheckRecall

@[expose] public section

universe u

/- 88.2.0.1: the category of inverse systems ⋯ ⟶ B₃ ⟶ B₂ ⟶ B₁ where each B_n is a
finite type A ⧸ I ^ n-algebra and each transition B_{n+1} ⟶ B_n is an A ⧸ I ^ (n + 1)-algebra
map inducing B_{n+1} ⧸ I ^ n B_{n+1} ≅ B_n. Morphisms are systems of homomorphisms. -/
@[stacks 0AL3] #check
  (AdicAlgebraSystem.{u} : ∀ (A : Type u) [CommRing A], Ideal A → Type (u + 1))
