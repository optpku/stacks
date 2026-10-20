module

public import Mathlib.Algebra.Group.Idempotent
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.TensorProduct.Maps

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Algebra.FinitePresentation

/-- A module-finite, finitely presented `A`-algebra `B` admits a finitely presented
parameter `A`-algebra carrying an idempotent that specializes to every idempotent
after arbitrary base change. -/
theorem exists_universalIdempotent (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B]
    [Algebra.FinitePresentation A B] :
    ∃ (Auniv : Type (max u v)) (_ : CommRing Auniv) (_ : Algebra A Auniv)
      (_ : Algebra.FinitePresentation A Auniv) (euniv : B ⊗[A] Auniv),
      IsIdempotentElem euniv ∧
        ∀ (A' : Type w) [CommRing A'] [Algebra A A'] (e : B ⊗[A] A'),
          IsIdempotentElem e →
            ∃ φ : Auniv →ₐ[A] A',
              Algebra.TensorProduct.map (AlgHom.id A B) φ euniv = e := sorry

end Algebra.FinitePresentation
