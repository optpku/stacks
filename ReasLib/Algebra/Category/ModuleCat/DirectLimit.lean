/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Direct limits of modules

This leaf keeps the concrete quotient and the categorical colimit in their existing Mathlib
owners.  It adds only the stage-equality bridge needed by the Stacks description and the canonical
comparison between the two presentations.

@stack 00D5
@stack 00D6
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ModuleCat

universe u v

noncomputable section

namespace DirectLimit.Module

variable {R : Type u} [Ring R]
variable {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable (M : I → Type v) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
variable (μ : ∀ i j, i ≤ j → M i →ₗ[R] M j)
variable [DirectedSystem M (μ · · ·)]

/-- The explicit eventual-equality criterion for the disjoint-union direct-limit presentation. -/
@[stacks 00D6 "direct-limit stage equality"]
theorem of_eq_iff {i j : I} {x : M i} {y : M j} :
    of R I M μ i x = of R I M μ j y ↔
      ∃ k, ∃ hik : i ≤ k, ∃ hjk : j ≤ k, μ i k hik x = μ j k hjk y := sorry

end DirectLimit.Module

namespace ModuleCat

variable {R : Type u} [Ring R]
variable {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable (M : I → Type v) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
variable (μ : ∀ i j, i ≤ j → M i →ₗ[R] M j)
variable [DirectedSystem M (μ · · ·)]

/-- Implementation pin only: Mathlib's concrete quotient is indexed by a `DecidableEq`, while the
textbook construction is noncomputable and has no mathematical decidability assumption. -/
local instance directLimit_decidableEq : DecidableEq I := Classical.decEq I

/-- Lemma 10.8.3: the categorical colimit of a directed system of modules is canonically
isomorphic to its explicit disjoint-union quotient presentation. -/
@[stacks 00D6 "direct-limit colimit comparison"]
noncomputable def directLimitColimitIso :
    colimit (directLimitDiagram M μ) ≅ ModuleCat.of R (_root_.DirectLimit M μ) :=
  colimit.isoColimitCocone
      (⟨directLimitCocone M μ, directLimitIsColimit M μ⟩ :
        ColimitCocone (directLimitDiagram M μ)) ≪≫
    (Module.DirectLimit.linearEquiv M μ).toModuleIso

/-- The comparison sends the categorical colimit leg to the canonical quotient map. -/
@[stacks 00D6 "direct-limit colimit comparison leg"]
theorem directLimitColimitIso_ι (i : I) :
    colimit.ι (directLimitDiagram M μ) i ≫ (directLimitColimitIso M μ).hom =
      ModuleCat.ofHom (DirectLimit.Module.of R I M μ i) := sorry

end ModuleCat

end
