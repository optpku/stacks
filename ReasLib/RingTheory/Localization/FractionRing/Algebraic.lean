/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Localization.Integral
import Mathlib.Tactic.CrossRefAttribute

/-!
# Algebraicity and Fraction Rings

@stack 0H7L
-/

@[expose] public section

universe u v w x

namespace Algebra.IsAlgebraic

variable {R : Type u} {S : Type v} {K : Type w} {L : Type x}
variable [CommRing R] [CommRing S] [IsDomain R]
variable [Field K] [CommRing L] [Algebra R S]
variable [Algebra R K] [IsFractionRing R K]
variable [Algebra S L] [IsFractionRing S L]
variable [Algebra K L] [Algebra R L]
variable [IsScalarTower R S L] [IsScalarTower R K L]

/-- Algebraicity of an extension descends from compatible fraction-ring presentations. -/
@[stacks 0H7L "algebraicity descends from fraction rings"]
theorem of_isFractionRing (h : Algebra.IsAlgebraic K L) :
    Algebra.IsAlgebraic R S := by
  have h' : Algebra.IsAlgebraic R L :=
    IsFractionRing.comap_isAlgebraic_iff.mpr h
  refine ⟨fun s ↦ (isAlgebraic_algHom_iff
    (IsScalarTower.toAlgHom R S L) (IsFractionRing.injective S L)).mp ?_⟩
  exact h'.isAlgebraic _

end Algebra.IsAlgebraic
