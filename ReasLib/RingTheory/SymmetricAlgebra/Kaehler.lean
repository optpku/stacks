/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Kahler differentials of symmetric algebras

@stack 07EV

This file records the conormal sequence associated to a finite-free presentation of the module of
generators of a symmetric algebra.
-/

@[expose] public section

open scoped TensorProduct
open Algebra

universe u v

namespace SymmetricAlgebra

variable {A : Type u} [CommRing A]
variable {M : Type v} [AddCommMonoid M] [Module A M]
variable {m : ℕ}

/-- Lemma 15.9.12 (1) (Stacks `07EV`): a surjection `q : A^{⊕ m} → M` presents the Kahler
differentials of `Sym_A(M)` by the base-changed kernel inclusion and the map induced by the
universal derivation. Equivalently, the displayed sequence ending in `Ω[Sym_A(M)⁄A] → 0` is
exact. -/
@[stacks 07EV]
theorem presentationConormalSequence_exact
    (q : (Fin m →₀ A) →ₗ[A] M) (hq : Function.Surjective q) :
    let C := SymmetricAlgebra A M
    let i : q.ker →ₗ[A] (Fin m →₀ A) := q.ker.subtype
    let toKaehler : C ⊗[A] (Fin m →₀ A) →ₗ[C] Ω[C⁄A] :=
      (KaehlerDifferential.D A C).tensorProductTo ∘ₗ
        (SymmetricAlgebra.ι A M).baseChange C ∘ₗ q.baseChange C
    Function.Exact (i.baseChange C) toKaehler ∧ Function.Surjective toKaehler := sorry

/-- Lemma 15.9.12 (2) (Stacks `07EV`): the universal derivation identifies
`Sym_A(M) ⊗[A] M` with `Ω[Sym_A(M)⁄A]`. -/
@[stacks 07EV]
theorem tensorToKaehler_bijective :
    Function.Bijective
      ((((KaehlerDifferential.D A (SymmetricAlgebra A M)).tensorProductTo).comp
        ((SymmetricAlgebra.ι A M).baseChange (SymmetricAlgebra A M))) :
          SymmetricAlgebra A M ⊗[A] M →ₗ[SymmetricAlgebra A M]
            Ω[SymmetricAlgebra A M⁄A]) := sorry

end SymmetricAlgebra
