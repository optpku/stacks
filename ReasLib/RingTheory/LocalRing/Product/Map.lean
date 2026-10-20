/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Data.Fintype.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Maps from finite products to local targets

This leaf records that a unital algebra map from a finite product factors
through a single coordinate when its target is local. The source factors need
not themselves be local.
-/

universe u v w x

namespace AlgHom

/-- A unital algebra homomorphism from a finite product factors through one coordinate when its
target is local. The index is recovered from the map itself, so no nonemptiness assumption on the
index type is needed. -/
@[stacks 04GG "local target selects a finite-product component"]
theorem exists_eq_comp_piEvalAlgHom_of_isLocalRing
    {R : Type u} {ι : Type v} {A : ι → Type w} {B : Type x}
    [CommSemiring R] [Finite ι]
    [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)]
    [Semiring B] [Algebra R B] [IsLocalRing B]
    (φ : (∀ i, A i) →ₐ[R] B) :
    ∃ i : ι, ∃ ψ : A i →ₐ[R] B,
      φ = ψ.comp (Pi.evalAlgHom R A i) := sorry

end AlgHom
