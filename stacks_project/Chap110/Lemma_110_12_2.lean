module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Data.Countable.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

universe u v

namespace Module.FinitePresentation

/-- Lemma 110.12.2: if `R` is a countable ring and `M` is a countable `R`-module,
then `M` is a finitely presented `R`-module if and only if the canonical map
`M ⊗[R] (ℕ → R) ⟶ (ℕ → M)` is an isomorphism. -/
@[stacks 0ALA]
theorem iff_piScalarRightHom_nat_bijective {R : Type u} [CommRing R] [Countable R]
    {M : Type v} [AddCommGroup M] [Module R M] [Countable M] :
    Module.FinitePresentation R M ↔
      Function.Bijective (TensorProduct.piScalarRightHom R R M ℕ) := sorry

end Module.FinitePresentation
