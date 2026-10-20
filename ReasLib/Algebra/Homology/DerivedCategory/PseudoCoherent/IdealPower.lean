/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Embedding
public import ReasLib.Algebra.Module.IdealPower.Predicate
import Mathlib.Tactic.CrossRefAttribute

/-!
# Detecting pseudo-coherent homology modulo a maximal ideal

@stack 0A7D
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace CategoryTheory.DerivedCategory.IsPseudoCoherent

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable {K : DerivedCategory (ModuleCat A)}

/-- Lemma 15.66.7 (0A7D): if degree-`i` homology remains nonzero modulo a maximal ideal, then it
is detected by a morphism to a finite single object annihilated by a power of that ideal. -/
@[stacks 0A7D]
theorem exists_finite_single_nonzero_of_mod_maximalIdeal_nontrivial
    (hK : K.IsPseudoCoherent) (i : ℤ) (𝔪 : Ideal A) [𝔪.IsMaximal]
    (hHi : Nontrivial
      (((DerivedCategory.homologyFunctor (ModuleCat A) i).obj K) ⧸
        (𝔪 • (⊤ : Submodule A
          ((DerivedCategory.homologyFunctor (ModuleCat A) i).obj K))))) :
    ∃ E : ModuleCat A,
      Module.Finite A E ∧ Module.IsAnnihilatedByPower 𝔪 E ∧
        ∃ α : K ⟶ (DerivedCategory.singleFunctor (ModuleCat A) i).obj E,
          DerivedCategory.homologyToSingle (R := A) i α ≠ 0 := sorry
-- Proof strategy: use the finite-presentation embedding from Lemma 15.66.6, apply Artin--Rees to
-- its homology image inside the target module, and quotient the target by a sufficiently high
-- power of `𝔪`; Nakayama's criterion preserves a nonzero homology class in the quotient.

end CategoryTheory.DerivedCategory.IsPseudoCoherent
