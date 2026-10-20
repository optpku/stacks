/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap49.Lemma_49_8_1
public import ReasLib.RingTheory.DedekindDifferent.Comparison
import StacksCheckRecall

@[expose] public section

open scoped Algebra.DualModule TensorProduct Algebra.TensorProduct.Right

universe u v

/- Lemma 49.8.2: if the Dedekind different of `A → B` is defined, then the
canonical trace-pairing map from `𝓛_{B/A}` to `Module.Dual A B`, the finite-case
relative dualizing module, is bijective. -/
@[stacks 0BW2] #check
  (Algebra.RelativeDualizingModule.dedekindComparison_bijective :
    ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
      [IsNoetherianRing A] [Module.Finite A B]
      (h_regular : ∀ a ∈ nonZeroDivisors A,
        algebraMap A B a ∈ nonZeroDivisors B)
      [Algebra.Etale (FractionRing A) (B ⊗[A] FractionRing A)],
      Function.Bijective
        (Algebra.RelativeDualizingModule.dedekindComparison A B))
