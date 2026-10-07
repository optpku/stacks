module

public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.RingTheory.Jacobson.Radical
public import Mathlib.RingTheory.Noetherian.Basic
public import ReasLib.LinearAlgebra.QuotientByIdeal

@[expose] public section

/-!
# Split linear maps detected modulo ideal powers

This file records the adic detection principle for split injections between
finite modules.  The hypothesis that splitting occurs for arbitrarily large
powers is represented by `Filter.Frequently` along `Filter.atTop`.
-/

open Filter

universe u v w

namespace LinearMap.QuotientByIdeal

variable {R : Type u} [CommRing R]
variable {N : Type v} [AddCommGroup N] [Module R N]
variable {M : Type w} [AddCommGroup M] [Module R M]

/-- A retraction after quotienting by `I` forces the kernel of the original
map to lie in `I N`. -/
@[stacks 02HO "kernel bound from a split ideal quotient"]
theorem ker_le_smul_of_retraction (I : Ideal R) (f : N →ₗ[R] M)
    (s : M ⧸ (I • (⊤ : Submodule R M)) →ₗ[R]
      N ⧸ (I • (⊤ : Submodule R N)))
    (hs : s.comp (f.quotientMapByIdeal I) = LinearMap.id) :
    LinearMap.ker f ≤ I • (⊤ : Submodule R N) := sorry

section Noetherian

variable [IsNoetherianRing R] [Module.Finite R N]

/-- If reductions of a map modulo arbitrarily large powers of an ideal in the
Jacobson radical split injectively, then the original map is injective. -/
@[stacks 02HO "injectivity detected by frequently split ideal-power quotients"]
theorem injective_of_frequently_split (I : Ideal R) (hI : I ≤ Ring.jacobson R)
    (f : N →ₗ[R] M)
    (hsplit : ∃ᶠ n : ℕ in atTop,
      ∃ s : M ⧸ (I ^ n • (⊤ : Submodule R M)) →ₗ[R]
        N ⧸ (I ^ n • (⊤ : Submodule R N)),
        s.comp (f.quotientMapByIdeal (I ^ n)) = LinearMap.id) :
    Function.Injective f := sorry

/-- A map between finite modules over a Noetherian ring has a retraction if
its reductions modulo arbitrarily large powers of an ideal in the Jacobson
radical have retractions. -/
@[stacks 02HO "split injection detected by ideal-power quotients"]
theorem exists_retraction_of_frequently_split [Module.Finite R M]
    (I : Ideal R) (hI : I ≤ Ring.jacobson R) (f : N →ₗ[R] M)
    (hsplit : ∃ᶠ n : ℕ in atTop,
      ∃ s : M ⧸ (I ^ n • (⊤ : Submodule R M)) →ₗ[R]
        N ⧸ (I ^ n • (⊤ : Submodule R N)),
        s.comp (f.quotientMapByIdeal (I ^ n)) = LinearMap.id) :
    ∃ s : M →ₗ[R] N, s.comp f = LinearMap.id := sorry

end Noetherian

end LinearMap.QuotientByIdeal
