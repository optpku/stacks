/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
      ∀ ⦃X : C⦄ (S : Subobject X), S ≠ ⊤ → ∃ f : G ⟶ X, ¬ S.Factors f := sorry

end CategoryTheory
