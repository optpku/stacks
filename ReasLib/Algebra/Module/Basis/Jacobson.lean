/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Nakayama
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Lifting bases through a Jacobson quotient

This leaf records the reusable basis-lifting interface behind the usual
Nakayama argument. The source of the chosen vectors is a set rather than a
submodule, so the result can be reused for submodule, ideal, and generating
family formulations alike.
-/

@[expose] public section

universe u v w

namespace Module.Basis

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/- The finite-free hypotheses are the canonical ambient assumptions; the index of the quotient
  basis is deliberately left arbitrary so callers do not have to rebuild a `Fin` reindexing. -/

/-- A basis of a finite free module modulo a Jacobson-radical ideal lifts to a basis upstairs whose
vectors are chosen from the same set. -/
@[stacks 03C1 "basis lifting through a Jacobson quotient"]
theorem exists_mem_of_quotient_basis
    [Module.Free R M] [Module.Finite R M]
    (J : Ideal R) (hJ : J ≤ Ring.jacobson R) (T : Set M)
    {ι : Type w}
    (b : Module.Basis ι (R ⧸ J) (M ⧸ (J • (⊤ : Submodule R M))))
    (hb : ∀ i, b i ∈ (J • (⊤ : Submodule R M)).mkQ '' T) :
    ∃ b' : Module.Basis ι R M, ∀ i, b' i ∈ T := sorry

end Module.Basis
