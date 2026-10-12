/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

import Mathlib.Tactic.CrossRefAttribute

/-!
# Split polynomial presentations after finite free base change

A finite algebra acquires a presentation by split one-variable relations after an injective finite
free extension of the base ring.

@stack 0531
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace Algebra

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]

/-- Lemma 15.21.3: after an injective finite free base change, a finite algebra is a quotient of a
polynomial algebra by separately split monic relations. -/
@[stacks 0531 "Lemma 15.21.3"]
theorem exists_finiteFree_baseChange_surjective_splitPolynomialQuotient :
    ∃ (n : ℕ) (R' : Type (max u v)) (_ : CommRing R') (_ : Algebra R R')
      (_ : Function.Injective (algebraMap R R')) (_ : Module.Finite R R')
      (_ : Module.Free R R') (d : Fin n → ℕ) (α : ∀ i, Fin (d i) → R'),
      ∃ φ :
        (MvPolynomial (Fin n) R' ⧸
          Ideal.span
            (Set.range fun i ↦
              ∏ j : Fin (d i), (MvPolynomial.X i - MvPolynomial.C (α i j)))) →ₐ[R']
          (R' ⊗[R] S),
        Function.Surjective φ := sorry

end Algebra
