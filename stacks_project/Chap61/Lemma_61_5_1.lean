/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.SpecializingLocalization
import Mathlib.Tactic.CrossRefAttribute
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry Localization

universe u

/- Lemma 61.5.1 (1): `Spec` of `specializing f I` maps by a homeomorphism onto
the points of `Spec(A)` specializing to `D(f) ∩ V(I)`. -/
@[stacks 096V] #check
  (Localization.Specializing.comap_range :
    ∀ {A : Type u} [CommRing A] (f : A) (I : Ideal A),
      Set.range (PrimeSpectrum.comap
        (algebraMap A (Localization.specializing f I))) =
        PrimeSpectrum.specializesTo
          (PrimeSpectrum.basicLocallyClosed f I))

section

variable {A : Type u} [CommRing A] (f : A) (I : Ideal A)

#check
  (PrimeSpectrum.localization_comap_isEmbedding
      (Localization.specializing f I) (Localization.specializingSubmonoid f I) :
    Topology.IsEmbedding (PrimeSpectrum.comap
      (algebraMap A (Localization.specializing f I))))

end

/- Lemma 61.5.1 (2): the `A`-algebra `specializing f I` depends only on the
underlying locally closed subset `D(f) ∩ V(I)`. -/
@[stacks 096V] #check
  (Localization.specializingSubmonoid_eq_of_basicLocallyClosed_eq :
    ∀ {A : Type u} [CommRing A] {f g : A} {I J : Ideal A},
      PrimeSpectrum.basicLocallyClosed f I =
        PrimeSpectrum.basicLocallyClosed g J →
      Localization.specializingSubmonoid f I =
        Localization.specializingSubmonoid g J)

/- Lemma 61.5.1 (3): `D(f) ∩ V(I)` is a closed subscheme of
`Spec(specializing f I)`, via `Spec.map` of the canonical surjection onto
`(A ⧸ I)_f`. -/
@[stacks 096V] #check
  (Localization.Specializing.specMap_toAwayQuotient :
    ∀ {A : Type u} [CommRing A] (f : A) (I : Ideal A),
      IsClosedImmersion
        (Spec.map (CommRingCat.ofHom
          (Localization.Specializing.toAwayQuotient f I))))

/- Lemma 61.5.1 (4): a ring map sending a standard locally closed subscheme
`Z'` into `Z` induces a unique `A`-algebra map of specializing localizations. -/
@[stacks 096V] #check
  (Localization.Specializing.existsUnique_map :
    ∀ {A : Type u} [CommRing A] {A' : Type u} [CommRing A']
      (φ : A →+* A') (f : A) (I : Ideal A) (f' : A') (I' : Ideal A'),
      Set.MapsTo (PrimeSpectrum.comap φ)
        (PrimeSpectrum.basicLocallyClosed f' I')
        (PrimeSpectrum.basicLocallyClosed f I) →
      ∃! ψ : Localization.specializing f I →+*
          Localization.specializing f' I',
        ψ.comp (algebraMap A (Localization.specializing f I)) =
          (algebraMap A' (Localization.specializing f' I')).comp φ)
