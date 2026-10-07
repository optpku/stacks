module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.RingTheory.Algebra.Quotient.BaseIdeal
public import ReasLib.RingTheory.Henselian.Pair.BaseChange
public import ReasLib.RingTheory.Henselian.Pair.Completion
public import stacks_project.Chap88.Lemma_88_8_4_EtaleOverComplement

/-!
# Algebraization of maps of adic completions through pair henselization

Lemma 88.8.7 records that an `A`-algebra map of `I`-adic completions from a
finite-type algebra étale over `Spec(A) \ V(I)` comes from a unique map into
the pair henselization of the target, and that every such map factors through
an étale algebra with isomorphic closed fiber.
-/

@[expose] public section

universe u

open Algebra RingPairCat

namespace Algebra.IsEtaleOverComplement

/-- Lemma 88.8.7 (1): Let `A` be a Noetherian ring, let `I` be an ideal of `A`,
and let `B` be a finite-type `A`-algebra such that `Spec(B) ⟶ Spec(A)` is
étale over `Spec(A) \ V(I)`. Let `C` be a Noetherian `A`-algebra. Then every
`A`-algebra map of `I`-adic completions `B^∧ ⟶ C^∧` comes from a unique
`A`-algebra map `B ⟶ C^h`, where `C^h` is the henselization of the pair
`(C, I C)`. -/
@[stacks 0AKJ]
theorem existsUnique_algHom {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [IsNoetherianRing A] [IsNoetherianRing C]
    [FiniteType A B] [henselianPairInclusion.IsRightAdjoint]
    (I : Ideal A) (hB : IsEtaleOverComplement I B)
    (φ : AdicCompletion (I.map (algebraMap A B)) B →ₐ[A]
      AdicCompletion (I.map (algebraMap A C)) C) :
    ∃! ψ : B →ₐ[A] henselizationRing (pairOfIdeal (I.map (algebraMap A C))),
      φ.toRingHom.comp (algebraMap B (AdicCompletion (I.map (algebraMap A B)) B)) =
        (henselizationToAdicCompletion
            (pairOfIdeal (I.map (algebraMap A C)))).comp ψ.toRingHom :=
  sorry

/-- Lemma 88.8.7 (2): Let `A` be a Noetherian ring, let `I` be an ideal of `A`,
and let `B` be a finite-type `A`-algebra such that `Spec(B) ⟶ Spec(A)` is
étale over `Spec(A) \ V(I)`. Let `C` be a Noetherian `A`-algebra. Then every
`A`-algebra map `B ⟶ C^h` into the henselization of `(C, I C)` factors through
an étale `C`-algebra `C'` such that `C / I C ⟶ C' / I C'` is an isomorphism. -/
@[stacks 0AKJ]
theorem exists_etaleFactor {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [IsNoetherianRing A] [IsNoetherianRing C]
    [FiniteType A B] [henselianPairInclusion.IsRightAdjoint]
    (I : Ideal A) (hB : IsEtaleOverComplement I B)
    (ψ : B →ₐ[A] henselizationRing (pairOfIdeal (I.map (algebraMap A C)))) :
    ∃ (C' : Type u) (_ : CommRing C') (_ : Algebra A C') (_ : Algebra C C')
      (_ : IsScalarTower A C C') (_ : Algebra.Etale C C'),
      Function.Bijective
          (AlgHom.BaseIdeal.quotientMap (IsScalarTower.toAlgHom A C C') I) ∧
        ∃ (τ : C' →ₐ[C] henselizationRing (pairOfIdeal (I.map (algebraMap A C))))
          (φ : B →ₐ[A] C'),
          ψ = (τ.restrictScalars A).comp φ :=
  sorry

end Algebra.IsEtaleOverComplement
