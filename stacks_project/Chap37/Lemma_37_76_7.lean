/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Algebra.FinitePresentation.UniversalIdempotent
import StacksCheckRecall

@[expose] public section

open scoped TensorProduct

universe u v w

/- Lemma 37.76.7: a finite, finitely presented `A`-algebra `B` admits a finitely
presented `A`-algebra carrying an idempotent that maps to every idempotent after
arbitrary base change. -/
@[stacks 0F3M] #check
  (Algebra.FinitePresentation.exists_universalIdempotent :
    ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
      [Module.Finite A B] [Algebra.FinitePresentation A B],
      ∃ (Auniv : Type (max u v)) (_ : CommRing Auniv) (_ : Algebra A Auniv)
        (_ : Algebra.FinitePresentation A Auniv) (euniv : B ⊗[A] Auniv),
        IsIdempotentElem euniv ∧
          ∀ (A' : Type w) [CommRing A'] [Algebra A A'] (e : B ⊗[A] A'),
            IsIdempotentElem e →
              ∃ φ : Auniv →ₐ[A] A',
                Algebra.TensorProduct.map (AlgHom.id A B) φ euniv = e)
