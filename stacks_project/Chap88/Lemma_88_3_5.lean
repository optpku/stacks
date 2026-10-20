/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.AdicCompletion.NaiveCotangent.JacobiZariski

@[expose] public section

universe u

open Algebra.NaiveCotangent.Adic

/- Lemma 88.3.5. The completed naive cotangent complexes of a tower of
adic, topologically finite type algebras have a six-term Jacobi–Zariski exact sequence. -/
@[stacks 0ALM] #check (Algebra.NaiveCotangent.Adic.jacobiZariski_exact :
  ∀ {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [IsNoetherianRing A]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    (I : Ideal A) [Algebra.TopologicallyFiniteType I B] [Algebra.TopologicallyFiniteType I C]
    {ι κ : Type u} [Fintype ι] [Fintype κ]
    (P : Presentation A B I ι) (Q : Presentation B C (I.map (algebraMap A B)) κ),
      Function.Exact (homologyOneTensor I P Q) (homologyOneMap I P Q) ∧
      Function.Exact (homologyOneMap I P Q) (δ I P Q) ∧
      Function.Exact (δ I P Q) (homologyZeroBaseChange I P Q) ∧
      Function.Exact (homologyZeroBaseChange I P Q) (homologyZeroMap I P Q) ∧
      Function.Surjective (homologyZeroMap I P Q))
