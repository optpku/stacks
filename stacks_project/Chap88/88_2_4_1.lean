/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.ClosedImmersion
import StacksCheckRecall

universe u

open scoped TensorProduct

@[expose] public section

/- 88.2.4.1: For `B` in C' over a Noetherian pair `(A, I)`, with `Ā = A ⧸ a`
and `Ī` cofinal with `I Ā`, closed-immersion base change is the quotient
identification `bar B = (B ⊗[A] Ā)^∧ = (B ⧸ aB)^∧ = B ⧸ aB`. -/
@[stacks 0AK1] #check (AdicCompletion.closedImmersionBaseChangeOfCofinal :
  ∀ {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (I a : Ideal A) [IsNoetherianRing A] [IsAdicComplete I B]
    [Algebra.FiniteType (A ⧸ I) (B ⧸ I.map (algebraMap A B))]
    (Ibar : Ideal (A ⧸ a)) {c d : ℕ} (hc : 0 < c) (hd : 0 < d)
    (hI : I.map (Ideal.Quotient.mk a) ^ c ≤ Ibar)
    (hIbar : Ibar ^ d ≤ I.map (Ideal.Quotient.mk a)),
    AdicCompletion (AdicCompletion.tensorIncludeRightIdeal B a Ibar)
        (B ⊗[A] (A ⧸ a)) ≃ₐ[A ⧸ a] B ⧸ a.map (algebraMap A B))
