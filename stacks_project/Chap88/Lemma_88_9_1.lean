module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Algebra.Quotient.BaseIdeal
public import stacks_project.Chap88.Lemma_88_8_4_EtaleOverComplement

/-!
# Filling an étale approximation over the complement of V(I)

Lemma 88.9.1 fills a finite-type étale-over-complement diagram along a
nilpotent quotient by a finite-type algebra that remains étale over the
complement and recovers the given special fiber.
-/

@[expose] public section

universe u

namespace Algebra.IsEtaleOverComplement

/-- Lemma 88.9.1: Let `A` be a Noetherian ring and `I` an ideal of `A`. Let
`J` be a nilpotent ideal of `A`. Suppose `C` is a finite-type `A`-algebra
such that `Spec(C) ⟶ Spec(A)` is étale over `Spec(A) \ V(I)`, and `B₀` is
a finite-type `(A ⧸ J)`-algebra such that `Spec(B₀) ⟶ Spec(A ⧸ J)` is étale
over `Spec(A ⧸ J) \ V(I (A ⧸ J))`. If `B₀ ⟶ C ⧸ JC` is étale and induces
an isomorphism `B₀ ⧸ I B₀ ≃ (C ⧸ JC) ⧸ I (C ⧸ JC)`, then the diagram can be
filled by a finite-type `A`-algebra `B` with `B ⧸ JB ≃ₐ[A ⧸ J] B₀`, with
`B ⟶ C` étale, and with `Spec(B) ⟶ Spec(A)` étale over `Spec(A) \ V(I)`. -/
@[stacks 0ALT]
theorem exists_liftApproximation
    {A C B₀ : Type u} [CommRing A] [IsNoetherianRing A] [CommRing C] [CommRing B₀]
    [Algebra A C] [Algebra.FiniteType A C] (I J : Ideal A) (hJ : IsNilpotent J)
    [Algebra (A ⧸ J) B₀] [Algebra.FiniteType (A ⧸ J) B₀]
    [Algebra B₀ (C ⧸ J.map (algebraMap A C))]
    [IsScalarTower (A ⧸ J) B₀ (C ⧸ J.map (algebraMap A C))]
    [Algebra.Etale B₀ (C ⧸ J.map (algebraMap A C))]
    (hC : IsEtaleOverComplement I C)
    (hB₀ : IsEtaleOverComplement (I.map (algebraMap A (A ⧸ J))) B₀)
    (hφ : Function.Bijective (AlgHom.BaseIdeal.quotientMap
      (IsScalarTower.toAlgHom (A ⧸ J) B₀ (C ⧸ J.map (algebraMap A C)))
      (I.map (algebraMap A (A ⧸ J))))) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B) (_ : Algebra.FiniteType A B)
      (_ : Algebra B C) (_ : IsScalarTower A B C) (_ : Algebra.Etale B C)
      (e : (B ⧸ J.map (algebraMap A B)) ≃ₐ[A ⧸ J] B₀),
      IsEtaleOverComplement I B ∧
        (IsScalarTower.toAlgHom (A ⧸ J) B₀
            (C ⧸ J.map (algebraMap A C))).comp e.toAlgHom =
          (IsScalarTower.toAlgHom A B C).quotientByBaseIdeal J :=
  sorry

end Algebra.IsEtaleOverComplement
