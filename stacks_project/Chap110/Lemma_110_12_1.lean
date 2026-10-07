module

public import Mathlib.Data.Countable.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

universe u v

namespace Module.Finite

/-- Lemma 110.12.1: a countable `R`-module `M` is a finite `R`-module if and only
if the canonical map `M ⊗[R] (ℕ → R) ⟶ (ℕ → M)` is surjective. -/
@[stacks 0AL9]
theorem iff_piScalarRightHom_nat_surjective {R : Type u} [CommSemiring R]
    {M : Type v} [AddCommMonoid M] [Module R M] [Countable M] :
    Module.Finite R M ↔
      Function.Surjective (TensorProduct.piScalarRightHom R R M ℕ) := sorry

end Module.Finite
