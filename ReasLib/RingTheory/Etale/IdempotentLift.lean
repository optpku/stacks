module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Etale-local lifting of idempotents

@stack 07LY
@stack 07M4

An idempotent modulo an ideal can be lifted after passing to an etale algebra whose closed fiber
is the original quotient.
-/

@[expose] public section

open scoped TensorProduct

universe u

namespace Algebra

variable {A : Type u} [CommRing A]

/-- Lemma 15.9.2 (Stacks `07LY`): an idempotent in `A ⧸ I` lifts to an idempotent after an etale
base change which induces an equivalence on the closed fiber. -/
@[stacks 07LY]
theorem exists_etale_idempotent_lift_of_quotient (I : Ideal A) (ebar : A ⧸ I)
    (hebar : IsIdempotentElem ebar) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (_ : Etale A A')
      (eIso : (A ⧸ I) ≃ₐ[A ⧸ I] (A' ⧸ Ideal.map (algebraMap A A') I)) (e' : A'),
      IsIdempotentElem e' ∧
        eIso ebar = Ideal.Quotient.mk (Ideal.map (algebraMap A A') I) e' := sorry

section IntegralBaseChange

universe v

variable {B : Type v} [CommRing B] [Algebra A B]

/-- The extension of `I` to `B` maps into its extension to a tensor-product base change. -/
theorem TensorProduct.map_le_comap_map_includeLeft (I : Ideal A) (A' : Type u)
    [CommRing A'] [Algebra A A'] :
    Ideal.map (algebraMap A B) I ≤
      (Ideal.map (algebraMap A (B ⊗[A] A')) I).comap
        (TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] A') := sorry

/-- The canonical map on quotients induced by the left inclusion into a tensor-product base
change. -/
@[stacks 07M4 "quotient map induced by tensor-product left inclusion"]
def TensorProduct.quotientIncludeLeft (I : Ideal A) (A' : Type u)
    [CommRing A'] [Algebra A A'] :
    (B ⧸ Ideal.map (algebraMap A B) I) →ₐ[A]
      ((B ⊗[A] A') ⧸ Ideal.map (algebraMap A (B ⊗[A] A')) I) :=
  Ideal.quotientMapₐ (Ideal.map (algebraMap A (B ⊗[A] A')) I)
    (TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] A')
    (TensorProduct.map_le_comap_map_includeLeft I A')

/-- The tensor-product quotient map sends a representative to its image under the left
inclusion. -/
@[simp]
theorem TensorProduct.quotientIncludeLeft_mk (I : Ideal A) (A' : Type u)
    [CommRing A'] [Algebra A A'] (b : B) :
    TensorProduct.quotientIncludeLeft (B := B) I A'
        (Ideal.Quotient.mk (Ideal.map (algebraMap A B) I) b) =
      Ideal.Quotient.mk (Ideal.map (algebraMap A (B ⊗[A] A')) I)
        ((TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] A') b) := sorry

/-- Lemma 15.9.10 (Stacks `07M4`): an idempotent in the closed fiber of an integral `A`-algebra
lifts after an etale base change which preserves the closed fiber. -/
@[stacks 07M4]
theorem exists_etale_idempotent_lift_of_integral_quotient [Algebra.IsIntegral A B]
    (I : Ideal A) (ebar : B ⧸ Ideal.map (algebraMap A B) I)
    (hebar : IsIdempotentElem ebar) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (_ : Etale A A')
      (_ : (A ⧸ I) ≃ₐ[A ⧸ I] (A' ⧸ Ideal.map (algebraMap A A') I))
      (e' : B ⊗[A] A'),
      IsIdempotentElem e' ∧
        TensorProduct.quotientIncludeLeft (B := B) I A' ebar =
          Ideal.Quotient.mk (Ideal.map (algebraMap A (B ⊗[A] A')) I) e' := sorry

end IntegralBaseChange

end Algebra
