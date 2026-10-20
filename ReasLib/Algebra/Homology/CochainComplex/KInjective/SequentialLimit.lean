/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.CochainComplex.KInjective.Limit
public import ReasLib.CategoryTheory.InverseSystem.Sequential

@[expose] public section

/-!
# K-Injective Sequential Limits

This leaf gives the cochain-complex form of the split-tower K-injectivity
criterion.  It is stated over `SequentialInverseSystem`, with explicit
degreewise limit assumptions, and is independent of derived-category choices.
-/

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v

namespace CategoryTheory.SequentialInverseSystem

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- Stacks 070L: the inverse limit of a sequential system of K-injective cochain complexes is
K-injective when successor maps are termwise split epimorphisms and all degreewise limits exist.
-/
@[stacks 070L]
theorem isKInjective_limit_of_termwiseSplitEpi
    (I : SequentialInverseSystem (CochainComplex 𝒜 ℤ))
    [∀ n : ℕ, (I.obj (op n)).IsKInjective]
    [∀ m : ℤ, HasLimit (I ⋙ HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) m)]
    (h_termwise_split_epi : ∀ n : ℕ, ∀ m : ℤ,
      IsSplitEpi ((I.transitionMap (Nat.le_succ n)).f m)) :
    (limit I).IsKInjective := sorry

end CategoryTheory.SequentialInverseSystem
