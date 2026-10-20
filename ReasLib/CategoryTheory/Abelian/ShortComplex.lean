/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Kernels and cokernels of morphisms of short complexes

The category of short complexes in an abelian category is itself abelian.  Consequently the
kernel and cokernel of a morphism are the canonical owners for the componentwise kernel and
cokernel rows.
-/

@[expose] public section

open CategoryTheory.Limits

universe v u

namespace CategoryTheory.ShortComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {S₁ S₂ : ShortComplex C}

/-- 08N6 (Lemma 12.5.16 (1)): if the source row is exact and the first map of the target row is
monic, then the canonical kernel short complex of the vertical morphism is exact. -/
@[stacks 08N6]
theorem kernel_exact_of_exact_of_mono (φ : S₁ ⟶ S₂) (hS₁ : S₁.Exact) [Mono S₂.f] :
    (kernel φ).Exact := sorry

/-- 08N6 (Lemma 12.5.16 (2)): if the target row is exact and the second map of the source row is
epic, then the canonical cokernel short complex of the vertical morphism is exact. -/
@[stacks 08N6]
theorem cokernel_exact_of_exact_of_epi (φ : S₁ ⟶ S₂) (hS₂ : S₂.Exact) [Epi S₁.g] :
    (cokernel φ).Exact := sorry

end CategoryTheory.ShortComplex

