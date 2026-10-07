module

public import stacks_project.Chap75.Lemma_75_13_3_Pullback

/-!
# Lemma 75.13.3

Tor-amplitude in a fixed interval, and finite Tor dimension, of a derived
`𝒪_X`-module may equivalently be tested after exact pullback along the
commutative presentation of ε from 75.4.0.1.
-/

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.Scheme.AssociatedModule
open AlgebraicGeometry.Scheme.SiteRestriction
open CategoryTheory
open RingedSite.Hom
open RingedSite.Hom.ModuleDerived

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.SiteRestriction

/-- Lemma 75.13.3 (1): for a scheme `X` and `E` in `D(𝒪_X)`, `E` has tor
amplitude in `[a, b]` if and only if `ε* E` has tor amplitude in `[a, b]`,
where `ε` is `commSmallEtaleToZariski` as in 75.4.0.1. -/
@[stacks 08HF]
theorem commSmallEtaleToZariski_hasTorAmplitudeIn_iff (X : Scheme.{u})
    (E : ModuleDerived.{u + 1} (smallCommRingedSite .zariski X)) (a b : ℤ) :
    HasTorAmplitudeIn E a b ↔
      HasTorAmplitudeIn ((commSmallEtaleToZariskiDerived X).obj E) a b :=
  sorry

/-- Lemma 75.13.3 (2): for a scheme `X` and `E` in `D(𝒪_X)`, `E` has finite
tor dimension if and only if `ε* E` has finite tor dimension, where `ε` is
`commSmallEtaleToZariski` as in 75.4.0.1. -/
@[stacks 08HF]
theorem commSmallEtaleToZariski_hasFiniteTorDimension_iff (X : Scheme.{u})
    (E : ModuleDerived.{u + 1} (smallCommRingedSite .zariski X)) :
    HasFiniteTorDimension E ↔
      HasFiniteTorDimension ((commSmallEtaleToZariskiDerived X).obj E) :=
  sorry

end AlgebraicGeometry.Scheme.SiteRestriction
