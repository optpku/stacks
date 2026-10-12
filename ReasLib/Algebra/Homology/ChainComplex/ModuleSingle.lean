/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Modules as Chain Complexes Concentrated in Degree Zero

@stack 00LQ

This file gives the standard degree-zero chain complex of a module a short reusable name.
-/

@[expose] public section

universe u v

namespace ChainComplex

/-- The chain complex of an `R`-module concentrated in degree zero. -/
@[stacks 00LQ "module concentrated in degree zero"]
noncomputable abbrev moduleSingle (R : Type u) [Ring R] (M : Type v)
    [AddCommGroup M] [Module R M] : ChainComplex (ModuleCat.{v} R) ℕ :=
  (single₀ (ModuleCat R)).obj (ModuleCat.of R M)

/-- A morphism to a module concentrated in degree zero vanishes in every positive degree. -/
@[stacks 00LQ "positive-degree component vanishing"]
theorem toModuleSingle_f_succ
    {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]
    {C : ChainComplex (ModuleCat.{v} R) ℕ}
    (f : C ⟶ moduleSingle R M) (n : ℕ) :
    f.f (n + 1) = 0 := sorry

end ChainComplex
