/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Cayley-Hamilton coefficients for finite modules

The Mathlib Cayley-Hamilton theorem records the coefficient condition in the
polynomial index. This leaf also exposes the source-oriented reindexing used
for ideal powers, so later arguments can choose either presentation without
reproving the bridge in a chapter file.

@stack 05G7
-/

@[expose] public section

universe u v

open Polynomial

namespace LinearMap

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- Lemma 10.16.3, tag `05G7`: a finite module endomorphism whose range lies in
`I • ⊤` has a monic annihilating polynomial whose coefficient at
`natDegree - j` belongs to `I ^ j` for every `j ≤ natDegree`. -/
@[stacks 05G7 "ideal-power coefficients in source order"]
theorem exists_monic_coeff_pow_of_range
    (φ : Module.End R M) {I : Ideal R}
    (hφ : LinearMap.range φ ≤ I • (⊤ : Submodule R M)) :
    ∃ p : R[X], p.Monic ∧
      (∀ j ≤ p.natDegree, p.coeff (p.natDegree - j) ∈ I ^ j) ∧
        Polynomial.aeval φ p = 0 := sorry

end LinearMap
