/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.BoundedAbove
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bounded-above relative pseudo-coherence criteria

@stack 0677

The results here are the presentationwise relative forms of the absolute
bounded-above criterion.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v

namespace CategoryTheory

/-- Lemma 15.82.9 (1): a bounded-above cochain complex whose term in degree `i` is
`(m - i)`-pseudo-coherent relative to `R` is `m`-pseudo-coherent relative to `R`. -/
@[stacks 0677 "(1), bounded-above relative m-pseudo-coherence"]
theorem cochainComplex_isMPseudoCoherentRelativeTo_of_boundedAbove_of_termwise
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (K : CochainComplex (ModuleCat A) ℤ) (m : ℤ)
    (h_bounded : CochainComplex.minus (ModuleCat A) K)
    (h_term : ∀ i : ℤ, (K.X i).IsMPseudoCoherentRelativeTo R (m - i)) :
    K.IsMPseudoCoherentRelativeTo R m := sorry

/-- Lemma 15.82.9 (2): a bounded-above cochain complex whose terms are pseudo-coherent relative
to `R` is pseudo-coherent relative to `R`. -/
@[stacks 0677 "(2), bounded-above relative pseudo-coherence"]
theorem cochainComplex_isPseudoCoherentRelativeTo_of_boundedAbove_of_termwise
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (K : CochainComplex (ModuleCat A) ℤ)
    (h_bounded : CochainComplex.minus (ModuleCat A) K)
    (h_term : ∀ i : ℤ, (K.X i).IsPseudoCoherentRelativeTo R) :
    K.IsPseudoCoherentRelativeTo R := sorry

end CategoryTheory
