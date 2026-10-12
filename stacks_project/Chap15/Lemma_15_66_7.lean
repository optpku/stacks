/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.IdealPower
import StacksCheckRecall

/-!
Lemma 15.66.7 (0A7D): nonzero homology modulo a maximal ideal is detected by a map to a finite
module annihilated by a power of that ideal.

@stack 0A7D
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

/- Lemma 15.66.7 (0A7D), with the maximal-ideal hypothesis visible as canonical instance data. -/
@[stacks 0A7D]
#check fun {A : Type u} [CommRing A] [IsNoetherianRing A]
    {K : DerivedCategory (ModuleCat A)} (hK : K.IsPseudoCoherent)
    (i : ℤ) (𝔪 : Ideal A) [𝔪.IsMaximal]
    (hHi : Nontrivial
      (((DerivedCategory.homologyFunctor (ModuleCat A) i).obj K) ⧸
        (𝔪 • (⊤ : Submodule A
          ((DerivedCategory.homologyFunctor (ModuleCat A) i).obj K))))) ↦
  (hK.exists_finite_single_nonzero_of_mod_maximalIdeal_nontrivial i 𝔪 hHi :
    ∃ E : ModuleCat A,
      Module.Finite A E ∧ Module.IsAnnihilatedByPower 𝔪 E ∧
        ∃ α : K ⟶ (DerivedCategory.singleFunctor (ModuleCat A) i).obj E,
          DerivedCategory.homologyToSingle (R := A) i α ≠ 0)
