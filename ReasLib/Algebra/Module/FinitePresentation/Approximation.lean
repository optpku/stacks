module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import ReasLib.LinearAlgebra.QuotientByIdeal

/-!
# Finite-presentation approximations modulo an ideal

This file records an approximation of a finite module by a finitely presented
module that is unchanged after reduction modulo a fixed ideal.
-/

@[expose] public section

universe u v

namespace Module.FinitePresentation

variable {B : Type u} [CommRing B]
variable {N : Type v} [AddCommGroup N] [Module B N]

/-- If `N` is finite over `B` and `B ⧸ I` is Noetherian, then `N` admits a
finitely presented surjective approximation whose reduction modulo `I` is
bijective. -/
theorem exists_approximation_mod_ideal (I : Ideal B)
    [Module.Finite B N] [IsNoetherianRing (B ⧸ I)] :
    ∃ (N' : Type u) (_ : AddCommGroup N') (_ : Module B N')
      (_ : Module.FinitePresentation B N') (π : N' →ₗ[B] N),
      Function.Surjective π ∧ Function.Bijective (π.quotientMapByIdeal I) := sorry

end Module.FinitePresentation
