module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness.AdicCompletion
public import ReasLib.RingTheory.AdicCompletion.Hausdorff
import Mathlib.Tactic.CrossRefAttribute

/-!
# Adic completeness, derived completeness, and separatedness

For a finitely generated ideal, ordinary adic completeness is equivalent to derived completeness
together with adic Hausdorffness.  The second theorem exposes the textbook intersection formula
for Hausdorffness.

@stack 091T
-/

@[expose] public section

universe u v

namespace ModuleCat

variable {A : Type u} [CommRing A]

/-- The reusable Hausdorff form of Proposition 15.92.5: for a finitely generated ideal `I`, an
`A`-module `M` is `I`-adically complete exactly when it is derived complete with respect to `I`
and `I`-adically Hausdorff. -/
@[stacks 091T "adic completeness via derived completeness and Hausdorffness"]
theorem isAdicComplete_iff_isDerivedCompleteWithRespectTo_and_isHausdorff
    (I : Ideal A) (hI : I.FG) (M : ModuleCat.{max u v, u} A) :
    IsAdicComplete I M ↔
      M.IsDerivedCompleteWithRespectTo I ∧ IsHausdorff I M := sorry

/-- Proposition 15.92.5 (091T), in the commutative-ring `ModuleCat` formalization: for a finitely
generated ideal `I`, an `A`-module `M` is `I`-adically complete exactly when it is derived complete
with respect to `I` and `⋂ n, I ^ n M = 0`. -/
@[stacks 091T "adic completeness via derived completeness and separatedness"]
theorem isAdicComplete_iff_isDerivedCompleteWithRespectTo_and_iInf_pow_smul_eq_bot
    (I : Ideal A) (hI : I.FG) (M : ModuleCat.{max u v, u} A) :
    IsAdicComplete I M ↔
      M.IsDerivedCompleteWithRespectTo I ∧
        (⨅ n : ℕ, (I ^ n) • (⊤ : Submodule A M) : Submodule A M) = ⊥ := sorry

end ModuleCat
