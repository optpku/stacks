module

public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.RingTheory.Completion.LocalRing
public import stacks_project.Chap90.Lemma_90_3_4_Length

/-!
# Length of a module over a local `Λ`-algebra

For a local `Λ`-algebra with residue field `k`, length over `Λ` differs from length
over `A` by the finite degree of `k` over `residueImage Λ k`. In the classical case the
degree is `1`.
-/

@[expose] public section

open Algebra

universe u v w

namespace IsLocalRing

/-- Lemma 90.3.4 (1): if `A` is a local `Λ`-algebra with residue field identified with `k`
and `M` is an `A`-module, then
`(Module.finrank (residueImage Λ k) k : ℕ∞) * Module.length A M = Module.length Λ M`. -/
@[stacks 06GG]
theorem length_mul_finrank_eq_length {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] {A : Type v} [CommRing A] [IsLocalRing A] [Algebra Λ A]
    (residueFieldIso : ResidueField A ≃ₐ[Λ] k) {M : Type w}
    [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower Λ A M] :
    (Module.finrank (residueImage Λ k) k : ℕ∞) * Module.length A M = Module.length Λ M :=
  sorry

/-- Lemma 90.3.4 (2): in the classical case, where `Λ` is a complete local Noetherian ring
with residue field `k`, one has `Module.length A M = Module.length Λ M`. -/
@[stacks 06GG]
theorem length_eq_of_classical {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ]
    [IsCompleteLocalRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (hsurj : Function.Surjective (algebraMap Λ k)) {A : Type v}
    [CommRing A] [IsLocalRing A] [Algebra Λ A]
    (residueFieldIso : ResidueField A ≃ₐ[Λ] k) {M : Type w}
    [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower Λ A M] :
    Module.length A M = Module.length Λ M :=
  sorry

end IsLocalRing
