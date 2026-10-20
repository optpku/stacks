/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# Quasi-isomorphisms between short exact rows of complexes

This file supplies the middle-map form of the two-out-of-three property for a morphism
between short exact rows of homological complexes. It complements
`HomologicalComplex.HomologySequence.quasiIso_τ₃` from Mathlib.
-/

@[expose] public section

open CategoryTheory

namespace HomologicalComplex.HomologySequence

variable {C ι : Type*} [Category* C] [Abelian C] {c : ComplexShape ι}
  {S₁ S₂ : ShortComplex (HomologicalComplex C c)}

/-- In a morphism between short exact rows of homological complexes, quasi-isomorphisms on
the two outer components force the middle component to be a quasi-isomorphism. -/
theorem quasiIso_τ₂ (φ : S₁ ⟶ S₂) (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)
    (h₁ : QuasiIso φ.τ₁) (h₃ : QuasiIso φ.τ₃) : QuasiIso φ.τ₂ := sorry


end HomologicalComplex.HomologySequence
