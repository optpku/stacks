/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness
public import ReasLib.Algebra.Module.IdealPower.Predicate
import Mathlib.Tactic.CrossRefAttribute

/-!
# Uniform annihilation of derived-complete power-torsion modules

A derived-complete module which is power-torsion for a finitely generated ideal is annihilated by
one uniform power of that ideal.

@stack 0CQY
-/

@[expose] public section

universe u v

namespace ModuleCat.IsDerivedCompleteWithRespectTo

variable {A : Type u} [CommRing A]

/-- Lemma 15.94.8 (Bhatt), Stacks `0CQY`: if `I` is finitely generated and `M` is both
`I`-power torsion and derived complete with respect to `I`, then a single power of `I`
annihilates `M`. -/
@[stacks 0CQY "uniform annihilation of a derived-complete power-torsion module"]
theorem exists_pow_smul_top_eq_bot_of_isIdealPowerTorsion
    (I : Ideal A) (M : ModuleCat.{max u v, u} A) (hI : I.FG)
    (hMtors : Module.IsIdealPowerTorsion I M)
    (hM : M.IsDerivedCompleteWithRespectTo I) :
    ∃ n : ℕ, (I ^ n) • (⊤ : Submodule A M) = ⊥ := sorry

end ModuleCat.IsDerivedCompleteWithRespectTo
