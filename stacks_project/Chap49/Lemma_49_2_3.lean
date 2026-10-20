/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.RelativeDualizing.Localization
import StacksCheckRecall

universe u v

open AlgebraicGeometry
open Algebra

/- Lemma 49.2.3 (1): if `A → B` factors through `Localization.Away f`, then
`ω_{B/A}` is canonically isomorphic to `ω_{B/Localization.Away f}`. -/
@[stacks 0BT2] #check (Algebra.RelativeDualizingModule.awayBaseIso :
  ∀ (A : Type u) (B' B : Type v)
    [CommRing A] [CommRing B'] [CommRing B]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B)
    [Module.Finite A B']
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
    (f : A) [Algebra (Localization.Away f) B]
    [IsScalarTower A (Localization.Away f) B],
    -- Local instance justification (instance diamond): the target action is induced by the selected factorization.
    letI : Algebra (Localization.Away (algebraMap A B' f)) B :=
      (RelativeDualizingModule.awayFactorMap A B' B f).toAlgebra
    -- Local instance justification (instance diamond): this localized action is selected locally because competing scalar actions exist.
    letI : Algebra (Localization.Away f)
        (Localization.Away (algebraMap A B' f)) :=
      Localization.Away.Relative.mapAlgebra (algebraMap A B') f
    -- Local instance justification (instance diamond): this localized action is selected locally because competing scalar actions exist.
    letI : IsScalarTower (Localization.Away f)
        (Localization.Away (algebraMap A B' f)) B :=
      RelativeDualizingModule.awayFactorMap_isScalarTower A B' B f
    -- Local instance justification (proof-local temporary data): this transported finiteness data is needed only for the localized comparison.
    letI : Module.Finite (Localization.Away f)
        (Localization.Away (algebraMap A B' f)) :=
      RelativeDualizingModule.finiteAwayBase A B' f
    RelativeDualizingModule.of A B' B h_quasiFinite h_open ≅
      RelativeDualizingModule.of (Localization.Away f)
        (Localization.Away (algebraMap A B' f)) B
          (RelativeDualizingModule.quasiFiniteAwayBase A B h_quasiFinite f)
          (RelativeDualizingModule.openAwayBase A B' B h_open f))

/- Lemma 49.2.3 (2): localizing `B` away from `g` identifies the localization of
`ω_{B/A}` with `ω_{Localization.Away g/A}`. -/
@[stacks 0BT2] #check (Algebra.RelativeDualizingModule.awayTargetIso :
  ∀ (A : Type u) (B' B : Type v)
    [CommRing A] [CommRing B'] [CommRing B]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B)
    [Module.Finite A B']
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
    (g : B),
    ModuleCat.of (Localization.Away g)
        (LocalizedModule.Away g
          (RelativeDualizingModule.of A B' B h_quasiFinite h_open)) ≅
      RelativeDualizingModule.of A B' (Localization.Away g)
        (RelativeDualizingModule.quasiFiniteAwayTarget A B h_quasiFinite g)
        (RelativeDualizingModule.openAwayTarget B' B h_open g))

/- Lemma 49.2.3 (3): simultaneously localizing source and target identifies
`ω_{B_f/A_f}` with the localization of `ω_{B/A}` away from `algebraMap A B f`. -/
@[stacks 0BT2] #check (Algebra.RelativeDualizingModule.awayIso :
  ∀ (A : Type u) (B' B : Type v)
    [CommRing A] [CommRing B'] [CommRing B]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (h_quasiFinite : Algebra.FiniteType.QuasiFinite A B)
    [Module.Finite A B']
    (h_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B' B))))
    (f : A),
    -- Local instance justification (instance diamond): this localized action is selected locally because competing scalar actions exist.
    letI : Algebra (Localization.Away f)
        (Localization.Away (algebraMap A B f)) :=
      Localization.Away.Relative.mapAlgebra (algebraMap A B) f
    -- Local instance justification (instance diamond): this localized action is selected locally because competing scalar actions exist.
    letI : IsScalarTower A (Localization.Away f)
        (Localization.Away (algebraMap A B f)) :=
      Localization.Away.Relative.algebraMapAlgebra_isScalarTower f
    let h_quasiFiniteTarget :=
      RelativeDualizingModule.quasiFiniteAwayTarget A B h_quasiFinite
        (algebraMap A B f)
    let h_openTarget :=
      RelativeDualizingModule.openAwayTarget B' B h_open (algebraMap A B f)
    -- Local instance justification (instance diamond): this localized action is selected locally because competing scalar actions exist.
    letI : Algebra (Localization.Away (algebraMap A B' f))
        (Localization.Away (algebraMap A B f)) :=
      (RelativeDualizingModule.awayFactorMap
        A B' (Localization.Away (algebraMap A B f)) f).toAlgebra
    -- Local instance justification (instance diamond): this localized action is selected locally because competing scalar actions exist.
    letI : Algebra (Localization.Away f)
        (Localization.Away (algebraMap A B' f)) :=
      Localization.Away.Relative.mapAlgebra (algebraMap A B') f
    -- Local instance justification (instance diamond): this localized action is selected locally because competing scalar actions exist.
    letI : IsScalarTower (Localization.Away f)
        (Localization.Away (algebraMap A B' f))
        (Localization.Away (algebraMap A B f)) :=
      RelativeDualizingModule.awayFactorMap_isScalarTower A B'
        (Localization.Away (algebraMap A B f)) f
    -- Local instance justification (proof-local temporary data): this transported finiteness data is needed only for the localized comparison.
    letI : Module.Finite (Localization.Away f)
        (Localization.Away (algebraMap A B' f)) :=
      RelativeDualizingModule.finiteAwayBase A B' f
    RelativeDualizingModule.of (Localization.Away f)
        (Localization.Away (algebraMap A B' f))
        (Localization.Away (algebraMap A B f))
          (RelativeDualizingModule.quasiFiniteAwayBase A
            (Localization.Away (algebraMap A B f)) h_quasiFiniteTarget f)
          (RelativeDualizingModule.openAwayBase A B'
            (Localization.Away (algebraMap A B f)) h_openTarget f) ≅
      ModuleCat.of (Localization.Away (algebraMap A B f))
        (LocalizedModule.Away (algebraMap A B f)
          (RelativeDualizingModule.of A B' B h_quasiFinite h_open)))
