module

public import Mathlib.RingTheory.Localization.Away.Basic
public import ReasLib.RingTheory.AdicCompletion.NaiveCotangent.CompletionPresentation
public import ReasLib.RingTheory.AdicCompletion.RigEtale
public import ReasLib.RingTheory.Algebra.Quotient.BaseIdeal
public import ReasLib.RingTheory.Henselian.Pair.BaseChange
public import ReasLib.RingTheory.Henselian.Pair.Completion
public import ReasLib.RingTheory.Etale.Complement
public import ReasLib.RingTheory.Ideal.OneAdd

/-!
# Rig-étale completions and étaleness away from a closed set
-/

@[expose] public section

universe u

open Algebra Algebra.NaiveCotangent.Adic

namespace Algebra.RigEtale

/-- A finite type algebra that is étale over the complement of `V(I)` has
rig-étale `I`-adic completion. -/
@[stacks 0ALQ]
theorem of_isEtaleOverComplement {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (B : Type u) [CommRing B] [Algebra A B] [FiniteType A B]
    (h : IsEtaleOverComplement I B) :
    RigEtale I (algebraCompletion I B) :=
  sorry

/-- A rig-étale `I`-adic completion yields an element congruent to `1` modulo
`I B` whose away-localization is étale over the complement of `V(I)`. -/
@[stacks 0ALQ]
theorem exists_mem_oneAdd_isEtaleOverComplement {A : Type u} [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) (B : Type u) [CommRing B] [Algebra A B]
    [FiniteType A B] [RigEtale I (algebraCompletion I B)] :
    ∃ g ∈ (I.map (algebraMap A B)).oneAdd,
      IsEtaleOverComplement I (Localization.Away g) :=
  sorry

end Algebra.RigEtale

open RingPairCat

namespace Algebra.IsEtaleOverComplement

/-- Every algebra map between the adic completions of a finite-type algebra étale away
from the base ideal and a Noetherian algebra uniquely descends to the pair Henselization
of the target, compatibly with the canonical map to its completion. -/
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

/-- Every algebra map from a finite-type algebra étale away from the base ideal to
the pair Henselization of a Noetherian algebra factors through an étale algebra over
the target that induces an isomorphism modulo the extended base ideal. -/
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
