/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.Embedding.Monoidal
import Mathlib.Tactic.CrossRefAttribute

/-!
# The monoidal embedding from chain degrees to cochain degrees

The standard embedding `ComplexShape.embeddingDownNat` sends a chain degree `n : ℕ` to the
cochain degree `-(n : ℤ)`.  This file registers its additive and tensor-sign compatibility, so
extension by zero along this embedding uses the generic monoidal API without local instances.
-/

@[expose] public section

namespace ComplexShape.embeddingDownNat

/-- The standard embedding `ComplexShape.embeddingDownNat` is additive on degrees. -/
@[stacks 0FP8 "additivity of the standard chain-to-cochain embedding"]
instance isAdditive :
    ComplexShape.Embedding.IsAdditive ComplexShape.embeddingDownNat := sorry

/-- The standard embedding `ComplexShape.embeddingDownNat` preserves the tensor signs on chain
and cochain complexes. -/
@[stacks 0FP8 "tensor signs for the standard chain-to-cochain embedding"]
instance preservesTensorSigns :
    ComplexShape.Embedding.PreservesTensorSigns ComplexShape.embeddingDownNat := sorry

/-- The additive homomorphism underlying `ComplexShape.embeddingDownNat` sends `n` to `-n`. -/
@[simp]
theorem addMonoidHom_apply (n : ℕ) :
    ComplexShape.Embedding.addMonoidHom ComplexShape.embeddingDownNat n =
      -(n : ℤ) := sorry

/-- The tensor sign in cochain degree `-n` is the usual sign `(-1) ^ n` in chain degree `n`. -/
@[simp]
theorem map_epsilon (n : ℕ) :
    (ComplexShape.up ℤ).ε (ComplexShape.embeddingDownNat.f n) =
      (-1 : ℤˣ) ^ n := sorry

end ComplexShape.embeddingDownNat

#synth ComplexShape.Embedding.IsAdditive ComplexShape.embeddingDownNat
#synth ComplexShape.Embedding.PreservesTensorSigns ComplexShape.embeddingDownNat
