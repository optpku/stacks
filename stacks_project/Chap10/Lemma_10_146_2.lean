/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.Unramified.LocalStructure
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.146.2
@stack 053K

The chapter retains the localization-of-étale hypothesis and the finite faithfully flat
extension explicitly.  Standard-étale shrinking and prime-localization calculations are proof
infrastructure; the local factorization and its source-facing unbundled view are the public API.
-/

open IsLocalRing

universe u v

namespace Algebra

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]

/-- A local refinement of Lemma 10.146.2: every maximal localization of the finite faithfully
flat extension admits a local `R`-algebra factorization from `S`. -/
@[stacks 053K "local factorization refinement"]
theorem existsFiniteFaithfullyFlatExtensionWithLocalFactorizations
    (hS :
      ∃ (T : Type (max u v)) (_ : CommRing T) (_ : Algebra R T) (_ : Algebra T S)
        (_ : IsScalarTower R T S) (_ : Algebra.Etale R T) (M : Submonoid T),
          IsLocalization M S) :
    ∃ (S' : Type (max u v)) (_ : CommRing S') (_ : Algebra R S')
      (_ : Module.Finite R S') (_ : Algebra.FinitePresentation R S')
      (_ : (algebraMap R S').FaithfullyFlat),
        ∀ m' : MaximalSpectrum S',
          ∃ φ : S →ₐ[R] Localization.AtPrime m'.asIdeal,
            IsLocalHom φ.toRingHom := sorry

/-- Lemma 10.146.2: if `S` is a localization of an étale `R`-algebra, then there is a finite,
finitely presented, faithfully flat `R`-algebra `S'` such that `R → S'_{ᵐ'}` factors through
`S` for every maximal ideal `ᵐ'` of `S'`. -/
@[stacks 053K]
theorem exists_finite_finitePresentation_faithfullyFlat_extension_with_factorizations
    (hS :
      ∃ (T : Type (max u v)) (_ : CommRing T) (_ : Algebra R T) (_ : Algebra T S)
        (_ : IsScalarTower R T S) (_ : Algebra.Etale R T) (M : Submonoid T),
          IsLocalization M S) :
    ∃ (S' : Type (max u v)) (_ : CommRing S') (_ : Algebra R S')
      (_ : Module.Finite R S') (_ : Algebra.FinitePresentation R S')
      (_ : (algebraMap R S').FaithfullyFlat),
        ∀ m' : MaximalSpectrum S',
          Nonempty (S →ₐ[R] Localization.AtPrime m'.asIdeal) := sorry

end


end Algebra

@[stacks 053K "standard-étale neighborhood owner"]
#check @Algebra.IsEtaleAt.exists_isStandardEtale

@[stacks 053K "local factorization refinement"]
#check @Algebra.existsFiniteFaithfullyFlatExtensionWithLocalFactorizations

@[stacks 053K "source-facing factorization"]
#check @Algebra.exists_finite_finitePresentation_faithfullyFlat_extension_with_factorizations

end
