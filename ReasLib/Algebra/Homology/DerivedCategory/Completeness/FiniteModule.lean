/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness
public import ReasLib.RingTheory.AdicCompletion.CompleteModule
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite derived-complete modules over Noetherian rings

For a derived-complete module with finite reduction modulo `I`, ordinary adic
completeness supplies the canonical action of `AdicCompletion I A`, and that
action makes the module finite over the completed ring.

@stack 09BA
-/

@[expose] public section

noncomputable section

universe u

namespace ModuleCat

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable {I : Ideal A} {M : ModuleCat A}

-- Local instance justification (instance diamond): the source conclusion uses
-- the named transported action, without exporting a competing module instance.
attribute [local instance] IsAdicComplete.completedModule

namespace IsDerivedCompleteWithRespectTo

/-- Lemma 15.95.5 (1): a derived-complete module over a Noetherian ring whose
reduction modulo `I` is finite is ordinarily `I`-adically complete. -/
@[stacks 09BA "(1), ordinary adic completeness"]
theorem isAdicComplete_of_finite_quotient
    (hM : M.IsDerivedCompleteWithRespectTo I)
    [Module.Finite (A ⧸ I) (M ⧸ I • (⊤ : Submodule A M))] :
    IsAdicComplete I M := sorry
-- Proof strategy: use derived completeness for surjectivity of the completion map, then apply
-- the Noetherian finite-reduction criterion to obtain injectivity and hence ordinary completeness.

/-- Lemma 15.95.5 (2): a derived-complete module over a Noetherian ring whose
reduction modulo `I` is finite is finite over `AdicCompletion I A` via its
canonical complete-module action. -/
@[stacks 09BA "(2), finiteness over the completed ring"]
theorem moduleFinite_over_adicCompletion_of_finite_quotient
    (hM : M.IsDerivedCompleteWithRespectTo I)
    [Module.Finite (A ⧸ I) (M ⧸ I • (⊤ : Submodule A M))] :
    -- Local instance justification (proof-local temporary data): install the
    -- preceding source clause only while exposing the canonical completed-ring action.
    let _ : IsAdicComplete I M :=
      isAdicComplete_of_finite_quotient hM
    Module.Finite (AdicCompletion I A) M := sorry
-- Proof strategy: install `isAdicComplete_of_finite_quotient hM` and apply
-- `IsAdicComplete.moduleFinite_of_finite_quotient` to the named completed-ring action.

/-- The ordinary completion of the module is finite over the completed ring
under the hypotheses of Lemma 15.95.5. -/
@[stacks 09BA "finiteness of the ordinary completed module"]
theorem moduleFinite_adicCompletion_of_finite_quotient
    (hM : M.IsDerivedCompleteWithRespectTo I)
    [Module.Finite (A ⧸ I) (M ⧸ I • (⊤ : Submodule A M))] :
    Module.Finite (AdicCompletion I A) (AdicCompletion I M) := sorry
-- Proof strategy: first obtain ordinary completeness and finiteness of `M` over the completed
-- ring, then transport that finite generating family across the canonical completion equivalence.

end IsDerivedCompleteWithRespectTo

end ModuleCat
