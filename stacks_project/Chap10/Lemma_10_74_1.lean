module

public import ReasLib.LinearAlgebra.QuotientByIdeal.Split
import StacksCheckRecall

/-!
# Lemma 10.74.1

@stack 02HO
-/

@[expose] public section

open Filter

universe u v w

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {N : Type v} [AddCommGroup N] [Module R N] [Module.Finite R N]
variable {M : Type w} [AddCommGroup M] [Module R M] [Module.Finite R M]
variable (I : Ideal R) (hI : I ≤ Ring.jacobson R) (f : N →ₗ[R] M)
variable (hsplit : ∃ᶠ n : ℕ in atTop,
  ∃ s : M ⧸ (I ^ n • (⊤ : Submodule R M)) →ₗ[R]
    N ⧸ (I ^ n • (⊤ : Submodule R N)),
    s.comp (f.quotientMapByIdeal (I ^ n)) = LinearMap.id)

/- Lemma 10.74.1: a map of finite modules over a Noetherian ring splits if
its reductions modulo arbitrarily large powers of an ideal in the Jacobson
radical split. -/
@[stacks 02HO]
#check (LinearMap.QuotientByIdeal.exists_retraction_of_frequently_split
    I hI f hsplit :
  ∃ s : M →ₗ[R] N, s.comp f = LinearMap.id)

#check (LinearMap.QuotientByIdeal.injective_of_frequently_split
    I hI f hsplit : Function.Injective f)

end
