/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.LinearAlgebra.Trace.CommutatorQuotient.FiniteProjective

/-!
# Finite-projective traces into the commutator quotient

The shared finite-projective trace extends the standard finite free trace,
with values in `R♮`.
-/

universe u v w

open Ring
open scoped Ring

#check (LinearMap.FiniteProjective.traceNatural :
    ∀ {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M],
    Module.End R M →+ R♮)

#check (LinearMap.FiniteProjective.traceNatural_eq_split :
    ∀ {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] {n : ℕ}
    (pi : (Fin n → R) →ₗ[R] M) (iota : M →ₗ[R] Fin n → R)
    (h_split : pi ∘ₗ iota = LinearMap.id) (f : Module.End R M),
    LinearMap.FiniteProjective.traceNatural f = LinearMap.traceNatural (iota ∘ₗ f ∘ₗ pi))

#check (LinearMap.FiniteProjective.traceNatural_free :
    ∀ {R : Type u} [Ring R] {n : Type v} [Fintype n] [DecidableEq n]
    [Module.Finite R (n → R)] [Module.Projective R (n → R)]
    (f : Module.End R (n → R)),
    LinearMap.FiniteProjective.traceNatural f = LinearMap.traceNatural f)

#check (LinearMap.FiniteProjective.traceNatural_comp_comm :
    ∀ {R : Type u} [Ring R] {M : Type v} {N : Type w}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N]
    (a : M →ₗ[R] N) (b : N →ₗ[R] M),
    LinearMap.FiniteProjective.traceNatural (a ∘ₗ b) =
      LinearMap.FiniteProjective.traceNatural (b ∘ₗ a))
