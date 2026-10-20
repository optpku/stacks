/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Etale.LiftApproximation
import StacksCheckRecall

universe u

/- Lemma 88.9.1: A finite-type étale approximation over the complement of a
closed set lifts along a nilpotent quotient with its prescribed special fiber. -/
@[stacks 0ALT] #check (Algebra.IsEtaleOverComplement.exists_liftApproximation :
    ∀
    {A C B₀ : Type u} [CommRing A] [IsNoetherianRing A] [CommRing C] [CommRing B₀]
    [Algebra A C] [Algebra.FiniteType A C] (I J : Ideal A) (hJ : IsNilpotent J)
    [Algebra (A ⧸ J) B₀] [Algebra.FiniteType (A ⧸ J) B₀]
    [Algebra B₀ (C ⧸ J.map (algebraMap A C))]
    [IsScalarTower (A ⧸ J) B₀ (C ⧸ J.map (algebraMap A C))]
    [Algebra.Etale B₀ (C ⧸ J.map (algebraMap A C))]
    (hC : Algebra.IsEtaleOverComplement I C)
    (hB₀ : Algebra.IsEtaleOverComplement (I.map (algebraMap A (A ⧸ J))) B₀)
    (hφ : Function.Bijective (AlgHom.BaseIdeal.quotientMap
      (IsScalarTower.toAlgHom (A ⧸ J) B₀ (C ⧸ J.map (algebraMap A C)))
      (I.map (algebraMap A (A ⧸ J))))),
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B) (_ : Algebra.FiniteType A B)
      (_ : Algebra B C) (_ : IsScalarTower A B C) (_ : Algebra.Etale B C)
      (e : (B ⧸ J.map (algebraMap A B)) ≃ₐ[A ⧸ J] B₀),
      Algebra.IsEtaleOverComplement I B ∧
        (IsScalarTower.toAlgHom (A ⧸ J) B₀
            (C ⧸ J.map (algebraMap A C))).comp e.toAlgHom =
          (IsScalarTower.toAlgHom A B C).quotientByBaseIdeal J)
