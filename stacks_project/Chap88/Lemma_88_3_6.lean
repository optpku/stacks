/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.AdicCompletion.NaiveCotangent.CompleteIntersection

/-!
# Lemma 88.3.6

Stagewise local complete intersection of `B ⧸ I^n B → C ⧸ I^n C` implies
injectivity of the Jacobi–Zariski map
`H^{-1}(NL_{B/A}^∧ ⊗[B] C) ⟶ H^{-1}(NL_{C/A}^∧)`.
-/

@[expose] public section

universe u

open Algebra.NaiveCotangent.Adic

/- Lemma 88.3.6: with assumptions as in Lemma 88.3.5, if each stage map
`B ⧸ I^n B → C ⧸ I^n C` is a local complete intersection homomorphism, then
`H^{-1}(NL_{B/A}^∧ ⊗[B] C) ⟶ H^{-1}(NL_{C/A}^∧)` is injective. -/
@[stacks 0AQJ] #check (Algebra.NaiveCotangent.Adic.homologyOneTensor_injective :
  ∀ {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [IsNoetherianRing A]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    (I : Ideal A) [Algebra.TopologicallyFiniteType I B] [Algebra.TopologicallyFiniteType I C]
    {ι κ : Type u} [Fintype ι] [Fintype κ]
    (P : Presentation A B I ι) (Q : Presentation B C (I.map (algebraMap A B)) κ)
    (h_lci : ∀ n : ℕ+,
      (CommAlgCat.adicQuotientMap I (IsScalarTower.toAlgHom A B C) n).IsLocalCompleteIntersection),
    Function.Injective (homologyOneTensor I P Q))
