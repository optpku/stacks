/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.LocalRing.Semilocal.Basis
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.78.8: bases inside a generating submodule

The reusable Jacobson-quotient and product-of-fields interfaces live in
`ReasLib`; this chapter file records the source-facing specialization.

@stack 03C1
-/

universe u v w

open IsLocalRing

section

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [IsLocalRing R] [Infinite (IsLocalRing.ResidueField R)]
variable [CommRing S] [Algebra R S] [Finite (MaximalSpectrum S)]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [Module.Free S M] [Module.Finite S M]

/- Lemma 10.78.8, tag `03C1`: if `N` generates `M` over `S`, then `N` contains an `S`-basis of
`M`, under the local, infinite-residue-field, and Jacobson-radical hypotheses. -/
@[stacks 03C1]
#check (Submodule.exists_basis_mem_of_span_eq_top :
  ∀ (N : Submodule R M),
    Ideal.map (algebraMap R S) (maximalIdeal R) ≤ Ring.jacobson S →
    Submodule.span S (N : Set M) = ⊤ →
    ∃ b : Module.Basis (Fin (Module.finrank S M)) S M, ∀ i, b i ∈ N)

end
