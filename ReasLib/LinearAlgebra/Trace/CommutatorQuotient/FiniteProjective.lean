module

public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.RingTheory.Finiteness.Projective
public import ReasLib.LinearAlgebra.Trace.CommutatorQuotient

/-!
# Finite-projective traces into the commutator quotient

The trace of a finite projective left module takes values in the additive
commutator quotient and agrees with the free trace for every splitting.
-/

@[expose] public section

noncomputable section

universe u v w

open Ring
open scoped Ring

namespace LinearMap.FiniteProjective

variable {R : Type u} [Ring R]

/-- The trace of an endomorphism of a finite projective left module, as an additive
map into the commutator quotient `R♮`. -/
noncomputable def traceNatural {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] :
    Module.End R M →+ R♮ :=
  let h := Module.Finite.exists_comp_eq_id_of_projective R M
  let pi := h.choose_spec.choose
  let iota := h.choose_spec.choose_spec.choose
  _root_.LinearMap.traceNatural.comp
    ((LinearMap.lcomp ℤ (Fin h.choose → R) pi).toAddMonoidHom.comp
      (LinearMap.compRight ℤ iota).toAddMonoidHom)

/-- The finite-projective trace equals the free-module trace of `iota ∘ₗ f ∘ₗ pi`
for any splitting `pi ∘ₗ iota = LinearMap.id`. -/
theorem traceNatural_eq_split {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] {n : ℕ}
    (pi : (Fin n → R) →ₗ[R] M) (iota : M →ₗ[R] Fin n → R)
    (h_split : pi ∘ₗ iota = LinearMap.id) (f : Module.End R M) :
    traceNatural f = _root_.LinearMap.traceNatural (iota ∘ₗ f ∘ₗ pi) := sorry

/-- On a standard finite free left module, the finite-projective trace agrees with
`LinearMap.traceNatural`. -/
theorem traceNatural_free {n : Type v} [Fintype n] [DecidableEq n]
    [Module.Finite R (n → R)] [Module.Projective R (n → R)]
    (f : Module.End R (n → R)) :
    traceNatural f = _root_.LinearMap.traceNatural f := sorry

/-- Cyclicity of the finite-projective trace: `Tr(a ∘ₗ b) = Tr(b ∘ₗ a)` in `R♮`. -/
theorem traceNatural_comp_comm {M : Type v} {N : Type w}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N]
    (a : M →ₗ[R] N) (b : N →ₗ[R] M) :
    traceNatural (a ∘ₗ b) = traceNatural (b ∘ₗ a) := sorry

end LinearMap.FiniteProjective
