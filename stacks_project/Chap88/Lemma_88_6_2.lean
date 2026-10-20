/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Henselian.PairHenselization.Algebraization
import StacksCheckRecall

@[expose] public section

universe u v w

/- Lemma 88.6.2: Let `I` be an ideal of a Noetherian ring `A`. Let `Ch` be a
henselization of a finite type `A`-algebra `C` with respect to the ideal
`Ideal.map (algebraMap A C) I`. Let `J` be an ideal of `Ch`. Then there exists
a finite type `A`-algebra `B` such that the `I`-adic completions satisfy
`B^∧ ≃ₐ[A] (Ch ⧸ J)^∧`. -/
@[stacks 0GAS] #check (IsPairHenselization.exists_finiteTypeAlgEquiv_quotient :
  ∀ {A : Type u} {C : Type v} {Ch : Type w}
    [CommRing A] [IsNoetherianRing A] [CommRing C] [CommRing Ch]
    [Algebra A C] [Algebra A Ch] [Algebra C Ch] [IsScalarTower A C Ch]
    [Algebra.FiniteType A C]
    (I : Ideal A) (Ih : Ideal Ch) (J : Ideal Ch)
    [IsPairHenselization C (Ideal.map (algebraMap A C) I) Ch Ih],
    ∃ (B : Type (max u v w)) (_ : CommRing B) (_ : Algebra A B)
      (_ : Algebra.FiniteType A B),
      Nonempty
        (AdicCompletion (Ideal.map (algebraMap A B) I) B ≃ₐ[A]
          AdicCompletion (Ideal.map (algebraMap A (Ch ⧸ J)) I) (Ch ⧸ J)))
