/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.RigEtale.Characterization
import StacksCheckRecall

universe u

/- Lemma 88.8.2: rig-étaleness is equivalent to derived and homological
annihilation, uniform annihilation at positive adic stages, full-size relation
and Jacobian conditions, and Jacobian and Cramer ideal power containments. -/
@[stacks 0AJU] #check (Algebra.RigEtale.tfae :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (B : Type u) [CommRing B] [Algebra A B]
    [Algebra.TopologicallyFiniteType I B] {ι : Type u} [Fintype ι]
    (P : Algebra.NaiveCotangent.Adic.Presentation A B I ι),
    List.TFAE
      [Algebra.RigEtale I B,
        ∃ c : ℕ, P.powSmulIdEqZero c,
        ∃ c : ℕ, P.homologyAnnihilated c,
        ∃ c : ℕ, P.stageHomologyAnnihilated c,
        P.existsRelationGenerators,
        P.existsElementarySquare,
        P.fittingContainsPow])
