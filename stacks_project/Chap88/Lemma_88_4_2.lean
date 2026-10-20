/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.RigSmooth.Characterization
import StacksCheckRecall

universe u

/- Lemma 88.4.2
Rig-smoothness is equivalent to derived Ext¹ annihilation, uniform scalar
factorization through the completed Jacobian, and a finite Jacobian cover. -/
@[stacks 0GAJ] #check (Algebra.RigSmooth.tfae :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (B : Type u) [CommRing B] [Algebra A B]
    [Algebra.TopologicallyFiniteType I B] {ι : Type u} [Fintype ι]
    (P : Algebra.NaiveCotangent.Adic.Presentation A B I ι),
    List.TFAE
      ([Algebra.RigSmooth I B,
        ∃ c : ℕ, CategoryTheory.twoTermExtOneAnnihilatedByIdeal
          (Algebra.NaiveCotangent.Adic.naiveCotangentObject I P)
          (I.map (algebraMap A B) ^ c),
        ∃ c : ℕ, ∀ a ∈ I ^ c, P.smulFactorsThroughJacobian a,
        P.HasJacobianCover]))
