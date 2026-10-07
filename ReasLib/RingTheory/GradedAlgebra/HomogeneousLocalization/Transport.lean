module

public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Homogeneous-localization transport

This leaf owns the equality-transport and degree-zero compatibility lemmas used by maps between
homogeneous localizations.  It is independent of Rees algebras and blowup charts.
-/

@[expose] public section

universe u v

namespace HomogeneousLocalization.Transport

/-- A graded ring map sends a degree-zero fraction to the corresponding degree-zero fraction. -/
@[stacks 00MQ "degree-zero homogeneous localization transport"]
theorem map_fromZeroRingHom
    {ι : Type*} [DecidableEq ι] [AddCommMonoid ι]
    {A : Type*} [CommRing A] {σ : Type*} [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ι → σ) [GradedRing 𝒜]
    {B : Type*} [CommRing B] {τ : Type*} [SetLike τ B] [AddSubgroupClass τ B]
    (ℬ : ι → τ) [GradedRing ℬ]
    (g : 𝒜 →+*ᵍ ℬ) {P : Submonoid A} {Q : Submonoid B} (h : P ≤ Q.comap g)
    (a : 𝒜 0) :
    HomogeneousLocalization.map g h (HomogeneousLocalization.fromZeroRingHom 𝒜 P a) =
      HomogeneousLocalization.fromZeroRingHom ℬ Q (g.gradedAddHom 0 a) := sorry

/-- `Away.map` preserves the degree-zero homogeneous localization map. -/
@[stacks 00MQ "degree-zero away transport"]
theorem awayMap_fromZeroRingHom
    {ι : Type*} [DecidableEq ι] [AddCommMonoid ι]
    {A : Type*} [CommRing A] {σ : Type*} [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ι → σ) [GradedRing 𝒜]
    {B : Type*} [CommRing B] {τ : Type*} [SetLike τ B] [AddSubgroupClass τ B]
    (ℬ : ι → τ) [GradedRing ℬ]
    (g : 𝒜 →+*ᵍ ℬ) (f : A) (a : 𝒜 0) :
    HomogeneousLocalization.Away.map g f
      (HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers f) a) =
      HomogeneousLocalization.fromZeroRingHom ℬ (Submonoid.powers (g f))
        (g.gradedAddHom 0 a) := sorry

/-- The ordinary localization value of a degree-zero homogeneous fraction is the numerator over
the unit denominator. -/
@[stacks 00MQ "degree-zero homogeneous localization value"]
theorem val_fromZeroRingHom
    {ι : Type*} [DecidableEq ι] [AddCommMonoid ι]
    {A : Type*} [CommRing A] {σ : Type*} [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ι → σ) [GradedRing 𝒜] (P : Submonoid A) (a : 𝒜 0) :
    HomogeneousLocalization.val (HomogeneousLocalization.fromZeroRingHom 𝒜 P a) =
      Localization.mk a.1 ⟨1, Submonoid.one_mem P⟩ := sorry

/-- Casting a homogeneous-localization ring hom along an equality of parameters commutes with
evaluation. -/
@[stacks 00MQ "homogeneous localization ring-hom cast evaluation"]
theorem cast_awayRingHom_apply
    {ι : Type*} [AddCommMonoid ι] [DecidableEq ι]
    {A : Type*} [CommRing A] {σ : Type*} [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ι → σ) [GradedRing 𝒜]
    {d : ι} {f g : 𝒜 d} {S : Type*} [CommRing S]
    (h : f = g) (φ : S →+* HomogeneousLocalization.Away 𝒜 (f : A)) (x : S) :
    cast (congrArg (fun y : 𝒜 d ↦ S →+* HomogeneousLocalization.Away 𝒜 (y : A)) h) φ x =
      cast (congrArg (fun y : 𝒜 d ↦ HomogeneousLocalization.Away 𝒜 (y : A)) h) (φ x) := sorry

/-- Casting an away-localization value along an equality of parameters commutes with its ordinary
localization value. -/
@[stacks 00MQ "homogeneous localization value cast"]
theorem cast_away_val
    {ι : Type*} [AddCommMonoid ι] [DecidableEq ι]
    {A : Type*} [CommRing A] {σ : Type*} [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ι → σ) [GradedRing 𝒜] {f g : A} (h : f = g)
    (x : HomogeneousLocalization.Away 𝒜 f) :
    HomogeneousLocalization.val (cast (congrArg (fun y ↦ HomogeneousLocalization.Away 𝒜 y) h) x) =
      cast (congrArg (fun y ↦ Localization.Away y) h) (HomogeneousLocalization.val x) := sorry

/-- The previous value-transport formula specialized to parameters in a graded piece. -/
@[stacks 00MQ "homogeneous localization subtype value cast"]
theorem cast_away_val_subtype
    {ι : Type*} [AddCommMonoid ι] [DecidableEq ι]
    {A : Type*} [CommRing A] {σ : Type*} [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ι → σ) [GradedRing 𝒜] {d : ι} {f g : 𝒜 d} (h : f = g)
    (x : HomogeneousLocalization.Away 𝒜 (f : A)) :
    HomogeneousLocalization.val
          (cast (congrArg (fun y : 𝒜 d ↦ HomogeneousLocalization.Away 𝒜 (y : A)) h) x) =
      cast (congrArg (fun y : 𝒜 d ↦ Localization.Away (y : A)) h)
        (HomogeneousLocalization.val x) := sorry

end HomogeneousLocalization.Transport
