module

import StacksCheckRecall
public import ReasLib.LinearAlgebra.TensorProduct.Pi.Countable

@[expose] public section

universe u v

variable {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Countable M]

/- Lemma 110.12.1: a countable `R`-module `M` is finite if and only if the
canonical map `M ⊗[R] (ℕ → R) ⟶ (ℕ → M)` is surjective. -/
@[stacks 0AL9] #check
  (Module.Finite.iff_piScalarRightHom_nat_surjective (R := R) (M := M) :
    Module.Finite R M ↔
      Function.Surjective (TensorProduct.piScalarRightHom R R M ℕ))
