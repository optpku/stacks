/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Module.Projective
public import ReasLib.Algebra.Module.StableFree
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Stable freeness in short exact sequences

@stack 0BC4

Finite stable freeness satisfies the expected two-out-of-three properties in a short exact
sequence.  Source-facing companions retain the ambient finite projective hypotheses on all three
terms.
-/

open CategoryTheory

universe u v

namespace CategoryTheory.ShortComplex.ShortExact

variable {R : Type u} [Ring R]
variable {S : ShortComplex (ModuleCat.{v} R)}

/-- If the outer terms of a short exact sequence are finite and stably free, then so is the
middle term. -/
theorem finiteStablyFree_X₂ (hS : S.ShortExact)
    [Module.Finite R S.X₁] [Module.StablyFree R S.X₁]
    [Module.Finite R S.X₃] [Module.StablyFree R S.X₃] :
    Module.Finite R S.X₂ ∧ Module.StablyFree R S.X₂ := sorry

/-- If the source and middle terms are finite and stably free and the target is projective, then
the target is finite and stably free. -/
theorem finiteStablyFree_X₃ (hS : S.ShortExact) [Module.Projective R S.X₃]
    [Module.Finite R S.X₁] [Module.StablyFree R S.X₁]
    [Module.Finite R S.X₂] [Module.StablyFree R S.X₂] :
    Module.Finite R S.X₃ ∧ Module.StablyFree R S.X₃ := sorry

/-- If the middle and target terms of a short exact sequence are finite and stably free, then so
is the source. -/
theorem finiteStablyFree_X₁ (hS : S.ShortExact)
    [Module.Finite R S.X₂] [Module.StablyFree R S.X₂]
    [Module.Finite R S.X₃] [Module.StablyFree R S.X₃] :
    Module.Finite R S.X₁ ∧ Module.StablyFree R S.X₁ := sorry

/-- Lemma 15.3.2 (1): in a short exact sequence of finite projective modules, stable freeness of
the outer terms implies stable freeness of the middle term. -/
@[stacks 0BC4 "(1)"]
theorem stablyFree_X₂ (hS : S.ShortExact)
    [Module.Finite R S.X₁] [Module.Projective R S.X₁]
    [Module.Finite R S.X₂] [Module.Projective R S.X₂]
    [Module.Finite R S.X₃] [Module.Projective R S.X₃]
    [Module.StablyFree R S.X₁] [Module.StablyFree R S.X₃] :
    Module.StablyFree R S.X₂ := sorry

/-- Lemma 15.3.2 (2): in a short exact sequence of finite projective modules, stable freeness of
the source and middle terms implies stable freeness of the target. -/
@[stacks 0BC4 "(2)"]
theorem stablyFree_X₃ (hS : S.ShortExact)
    [Module.Finite R S.X₁] [Module.Projective R S.X₁]
    [Module.Finite R S.X₂] [Module.Projective R S.X₂]
    [Module.Finite R S.X₃] [Module.Projective R S.X₃]
    [Module.StablyFree R S.X₁] [Module.StablyFree R S.X₂] :
    Module.StablyFree R S.X₃ := sorry

/-- Lemma 15.3.2 (3): in a short exact sequence of finite projective modules, stable freeness of
the middle and target terms implies stable freeness of the source. -/
@[stacks 0BC4 "(3)"]
theorem stablyFree_X₁ (hS : S.ShortExact)
    [Module.Finite R S.X₁] [Module.Projective R S.X₁]
    [Module.Finite R S.X₂] [Module.Projective R S.X₂]
    [Module.Finite R S.X₃] [Module.Projective R S.X₃]
    [Module.StablyFree R S.X₂] [Module.StablyFree R S.X₃] :
    Module.StablyFree R S.X₁ := sorry

end CategoryTheory.ShortComplex.ShortExact
