/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.BaseChange.Flat
public import stacks_project.Chap10.Lemma_10_65_1
import StacksCheckRecall

/-!
# Associated primes after flat base change

@stack 0312

The reusable statements are owned by
`ReasLib.RingTheory.Ideal.AssociatedPrime.BaseChange.Flat`.  The import of Lemma 10.65.1 is
retained temporarily for chapter-level downstream compatibility; the library owner has no
chapter dependency.
-/

@[expose] public section

open scoped TensorProduct Algebra.TensorProduct.Right

universe u v w x

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module R M]
variable {N : Type x} [AddCommGroup N] [Module S N] [Module R N]
variable [IsScalarTower R S N] [Module.Flat R N]

@[stacks 0312 "(1), flat-base-change inclusion"]
#check (associatedPrimesOfModule.BaseChange.Flat.iUnion_quotient_subset
  (R := R) (S := S) (M := M) (N := N) :
    (⋃ p ∈ associatedPrimesOfModule R M,
      associatedPrimesOfModule S
        (N ⧸ (p.map (algebraMap R S) • (⊤ : Submodule S N)))) ⊆
      associatedPrimesOfModule S (N ⊗[R] M))

variable [IsNoetherianRing R]

@[stacks 0312 "(2), Noetherian equality"]
#check (associatedPrimesOfModule.BaseChange.Flat.tensor_eq_iUnion_quotient
  (R := R) (S := S) (M := M) (N := N) :
    associatedPrimesOfModule S (N ⊗[R] M) =
      ⋃ p ∈ associatedPrimesOfModule R M,
        associatedPrimesOfModule S
          (N ⧸ (p.map (algebraMap R S) • (⊤ : Submodule S N))))

end
