/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Balanced
public import Mathlib.CategoryTheory.Generator.Preadditive
public import Mathlib.CategoryTheory.Subobject.Limits
import Mathlib.Tactic.CrossRefAttribute

/-!
# Separators detected by proper subobjects

This file relates the canonical separator predicate to the condition that every proper
subobject misses a morphism from the proposed generator.  The result only uses the
preadditive, balanced, and kernel structure needed by the argument.
-/

@[expose] public section

open CategoryTheory.Limits

universe v u

namespace CategoryTheory

/-- An object in a balanced preadditive category with kernels is a separator exactly when
every proper subobject fails to contain the image of some morphism from that object. -/
@[stacks 079B "generator subobject criterion"]
theorem isSeparator_iff_exists_not_factors_subobject
    (C : Type u) [Category.{v} C] [Preadditive C] [Balanced C] [HasKernels C]
    (G : C) :
    IsSeparator G ↔
      ∀ ⦃X : C⦄ (S : Subobject X), S ≠ ⊤ → ∃ f : G ⟶ X, ¬ S.Factors f := by
  classical
  constructor
  · intro hG X S hS
    by_contra! h
    have hE : Epi S.arrow := ⟨fun a b hab ↦ hG.def a b (fun f ↦ by
      rw [← S.factorThru_arrow f (h f)]
      simpa only [Category.assoc] using congrArg (fun k ↦ S.factorThru f (h f) ≫ k) hab)⟩
    exact hS ((Subobject.isIso_arrow_iff_eq_top S).mp
      ((isIso_iff_mono_and_epi S.arrow).mpr ⟨inferInstance, hE⟩))
  · intro h
    rw [Preadditive.isSeparator_iff]
    intro X Y f hf
    by_contra hne
    have hkernel : kernelSubobject f ≠ ⊤ := by
      intro heq
      have hh := (kernelSubobject_factors_iff f (𝟙 X)).mp
        (heq ▸ Subobject.top_factors (𝟙 X))
      exact hne (by simpa using hh)
    obtain ⟨g, hg⟩ := h (kernelSubobject f) hkernel
    exact hg (kernelSubobject_factors f g (hf g))

end CategoryTheory
