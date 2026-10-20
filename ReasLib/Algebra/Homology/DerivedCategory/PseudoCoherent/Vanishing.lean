/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Cohomology
import Mathlib.Tactic.CrossRefAttribute

/-!
# Vanishing criteria for pseudo-coherence

This leaf owns the three atomic cochain-complex criteria of Stacks `064W`.  They are stated for an
arbitrary `Ring`, with the concrete homology objects and finiteness hypotheses visible at the
surface; no truncation or representative data is hidden behind a choice.

@stack 064W
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.CochainComplex

variable {R : Type u} [Ring R]

/-- Lemma 15.65.7 (1): vanishing homology in all degrees `i ≥ m` implies `m`-pseudo-coherence. -/
@[stacks 064W "(1), vanishing above and at m"]
theorem isMPseudoCoherent_of_homology_isZero_ge
    {K : CochainComplex (ModuleCat R) ℤ} {m : ℤ}
    (hvanish : ∀ i : ℤ, m ≤ i → IsZero (K.homology i)) :
    K.IsMPseudoCoherent m := sorry

/-- Lemma 15.65.7 (2): vanishing above `m` and finite top homology imply `m`-pseudo-coherence. -/
@[stacks 064W "(2), finite top homology"]
theorem isMPseudoCoherent_of_homology_isZero_gt_and_finite
    {K : CochainComplex (ModuleCat R) ℤ} {m : ℤ}
    (hvanish : ∀ i : ℤ, m < i → IsZero (K.homology i))
    (hm : Module.Finite R (K.homology m)) :
    K.IsMPseudoCoherent m := sorry

/-- Lemma 15.65.7 (3): vanishing above `m + 1`, finite presentation in degree `m + 1`, and
finite top homology imply `m`-pseudo-coherence. -/
@[stacks 064W "(3), finite top and next homology"]
theorem isMPseudoCoherent_of_homology_isZero_gt_add_one_and_finite
    {K : CochainComplex (ModuleCat R) ℤ} {m : ℤ}
    (hvanish : ∀ i : ℤ, m + 1 < i → IsZero (K.homology i))
    (hm_succ : Module.FinitePresentation R (K.homology (m + 1)))
    (hm : Module.Finite R (K.homology m)) :
    K.IsMPseudoCoherent m := sorry

end CategoryTheory.CochainComplex
