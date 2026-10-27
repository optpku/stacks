/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Standard
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.Stability

/-!
# Standard restrictions of chosen big sites

This module restricts a chosen presentation of the big fppf site to each of
the five standard scheme precoverages while retaining its carrier and seed
schemes.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry

namespace StandardTopology

/-- The canonical scheme precoverage associated to a standard topology. -/
def precoverage (τ : StandardTopology) : Precoverage Scheme.{u} :=
  match τ with
  | .zariski => Scheme.zariskiPrecoverage
  | .etale => Scheme.etalePrecoverage
  | .smooth => Scheme.bigSmoothPrecoverage
  | .syntomic => Scheme.bigSyntomicPrecoverage
  | .fppf => Scheme.fppfPrecoverage

/-- Every standard scheme precoverage is contained in the fppf precoverage. -/
theorem precoverage_le_fppfPrecoverage (τ : StandardTopology) :
    τ.precoverage ≤ Scheme.fppfPrecoverage := by
  cases τ with
  | zariski => exact Scheme.zariskiPrecoverage_le_fppfPrecoverage
  | etale | smooth =>
      apply Scheme.precoverage_mono
      intro S T f hf
      letI := hf
      exact ⟨⟨fun {_} hU {_} hV e => (f.smooth_appLE hU hV e).flat⟩,
        ⟨fun {_} hU {_} hV e => (f.smooth_appLE hU hV e).finitePresentation⟩⟩
  | syntomic =>
      apply Scheme.precoverage_mono
      intro S T f hf
      constructor
      · show Flat f
        apply (HasRingHomProperty.iff_exists_appLE (P := @Flat)
          (RingHom.Flat.stableUnderComposition.stableUnderCompositionWithLocalizationAway
            RingHom.Flat.holdsForLocalizationAway).left).mpr
        intro x
        obtain ⟨U, hx, V, e, h⟩ := hf.property x
        exact ⟨V, U, hx, e, h.1⟩
      · show LocallyOfFinitePresentation f
        apply (HasRingHomProperty.iff_exists_appLE (P := @LocallyOfFinitePresentation)
          (RingHom.finitePresentation_stableUnderComposition.stableUnderCompositionWithLocalizationAway
            RingHom.finitePresentation_holdsForLocalizationAway).left).mpr
        intro x
        obtain ⟨U, hx, V, e, h⟩ := hf.property x
        exact ⟨V, U, hx, e, h.2.1⟩
  | fppf => exact le_rfl

end StandardTopology

namespace ChosenBigSite

/-- The precoverage obtained by restricting a chosen fppf pretopology to a
standard scheme precoverage. -/
def standardPrecoverage
    (X : ChosenBigSite.{u, v} Scheme.fppfPrecoverage) (τ : StandardTopology) :
    Precoverage X.carrier :=
  (@Pretopology.toPrecoverage X.carrier (Cat.str X.carrier) X.hasPullbacks
    X.pretopology) ⊓ τ.precoverage.comap X.toScheme

/-- The selected covering families that remain after restriction to a
standard scheme precoverage. -/
def standardSeedCoverings
    (X : ChosenBigSite.{u, v} Scheme.fppfPrecoverage) (τ : StandardTopology)
    (T : X.carrier) : Set (Presieve T) :=
  X.seedCoverings T ∩ X.standardPrecoverage τ T

/-- Membership in the restricted selected covering families is membership in
the original selection together with the restricted precoverage. -/
theorem mem_standardSeedCoverings_iff
    (X : ChosenBigSite.{u, v} Scheme.fppfPrecoverage) (τ : StandardTopology)
    {T : X.carrier} {R : Presieve T} :
    R ∈ X.standardSeedCoverings τ T ↔
      R ∈ X.seedCoverings T ∧ R ∈ X.standardPrecoverage τ T := Iff.rfl

/-- Singleton isomorphisms cover in every restricted standard precoverage. -/
theorem standardPrecoverage_hasIsos
    (X : ChosenBigSite.{u, v} Scheme.fppfPrecoverage) (τ : StandardTopology) :
    ∀ ⦃S T : X.carrier⦄ (f : S ⟶ T) [IsIso f],
      Presieve.singleton f ∈ X.standardPrecoverage τ T := by
  letI := X.hasPullbacks
  letI : MorphismProperty.ContainsIdentities (@Smooth : MorphismProperty Scheme.{u}) :=
    ⟨fun _ => inferInstance⟩
  haveI : τ.precoverage.HasIsos := by
    cases τ with
    | fppf =>
        refine ⟨fun {_ _} f _ => ?_⟩
        exact Scheme.zariskiPrecoverage_le_fppfPrecoverage _
          (Precoverage.mem_coverings_of_isIso (J := Scheme.zariskiPrecoverage) f)
    | zariski | etale | smooth | syntomic =>
        dsimp only [StandardTopology.precoverage, Scheme.etalePrecoverage]
        infer_instance
  intro S T f _
  exact ⟨X.pretopology.has_isos f, Precoverage.mem_coverings_of_isIso f⟩

/-- Restricted standard covering families are stable under the chosen
pullbacks. -/
theorem standardPrecoverage_pullbacks
    (X : ChosenBigSite.{u, v} Scheme.fppfPrecoverage) (τ : StandardTopology) :
    ∀ ⦃S T : X.carrier⦄ (f : S ⟶ T) (R : Presieve T),
      R ∈ X.standardPrecoverage τ T →
        @Presieve.pullbackArrows X.carrier (Cat.str X.carrier) T S f R
          ⟨fun _ => X.hasPullbacks.has_limit _⟩ ∈ X.standardPrecoverage τ S := by
  letI := X.hasPullbacks
  letI := X.spec.toScheme_preservesPullbacks
  haveI : τ.precoverage.IsStableUnderBaseChange := by
    cases τ <;>
      dsimp only [StandardTopology.precoverage, Scheme.etalePrecoverage,
        Scheme.fppfPrecoverage] <;> infer_instance
  intro S T f R hR
  exact ⟨X.pretopology.pullbacks f R hR.1,
    Precoverage.pullbackArrows_mem (J := τ.precoverage.comap X.toScheme) f hR.2⟩

/-- Restricted standard covering families are stable under composition. -/
theorem standardPrecoverage_transitive
    (X : ChosenBigSite.{u, v} Scheme.fppfPrecoverage) (τ : StandardTopology) :
    ∀ ⦃T : X.carrier⦄ (R : Presieve T)
      (Rᵢ : ∀ ⦃S : X.carrier⦄ (f : S ⟶ T), R f → Presieve S),
      R ∈ X.standardPrecoverage τ T →
        (∀ ⦃S : X.carrier⦄ (f : S ⟶ T) (h : R f),
          Rᵢ f h ∈ X.standardPrecoverage τ S) →
            R.bind Rᵢ ∈ X.standardPrecoverage τ T := by
  letI := X.hasPullbacks
  letI := X.spec.toScheme_preservesPullbacks
  letI : MorphismProperty.ContainsIdentities (@Smooth : MorphismProperty Scheme.{u}) :=
    ⟨fun _ => inferInstance⟩
  haveI : τ.precoverage.HasIsos := by
    cases τ with
    | fppf =>
        refine ⟨fun {_ _} f _ => ?_⟩
        exact Scheme.zariskiPrecoverage_le_fppfPrecoverage _
          (Precoverage.mem_coverings_of_isIso (J := Scheme.zariskiPrecoverage) f)
    | zariski | etale | smooth | syntomic =>
        dsimp only [StandardTopology.precoverage, Scheme.etalePrecoverage]
        infer_instance
  haveI : τ.precoverage.IsStableUnderBaseChange := by
    cases τ <;>
      dsimp only [StandardTopology.precoverage, Scheme.etalePrecoverage,
        Scheme.fppfPrecoverage] <;> infer_instance
  haveI : τ.precoverage.IsStableUnderComposition := by
    cases τ <;>
      dsimp only [StandardTopology.precoverage, Scheme.etalePrecoverage,
        Scheme.fppfPrecoverage] <;> infer_instance
  intro T R Rᵢ hR hRᵢ
  exact ⟨X.pretopology.transitive R Rᵢ hR.1 (fun _ f h => (hRᵢ f h).1),
    (τ.precoverage.comap X.toScheme).toPretopology.transitive R Rᵢ hR.2
      (fun _ f h => (hRᵢ f h).2)⟩

/-- The pretopology obtained by restricting a chosen fppf presentation to a
standard scheme precoverage. -/
def standardPretopology
    (X : ChosenBigSite.{u, v} Scheme.fppfPrecoverage) (τ : StandardTopology) :
    @Pretopology X.carrier (Cat.str X.carrier) X.hasPullbacks :=
  @Pretopology.mk X.carrier (Cat.str X.carrier) X.hasPullbacks
    (X.standardPrecoverage τ) (fun {_ _} f => X.standardPrecoverage_hasIsos τ f)
    (fun {_ _} f R hR => X.standardPrecoverage_pullbacks τ f R hR)
    (fun {_} R Rᵢ hR hRᵢ => X.standardPrecoverage_transitive τ R Rᵢ hR hRᵢ)

/-- The restricted seeds and pretopology present the selected standard scheme
precoverage. -/
theorem standardSite_specification
    (X : ChosenBigSite.{u, v} Scheme.fppfPrecoverage) (τ : StandardTopology) :
    IsChosenBigSite τ.precoverage X.carrier X.hasPullbacks X.toScheme X.seedSchemes
      (X.standardSeedCoverings τ) (X.standardPretopology τ) := sorry

/-- Restrict a chosen fppf-site presentation to a standard scheme
precoverage, retaining its carrier, scheme functor, and seed schemes. -/
def standardSite
    (X : ChosenBigSite.{u, v} Scheme.fppfPrecoverage) (τ : StandardTopology) :
    ChosenBigSite τ.precoverage where
  carrier := X.carrier
  hasPullbacks := X.hasPullbacks
  toScheme := X.toScheme
  fullyFaithful := X.fullyFaithful
  seedSchemes := X.seedSchemes
  seedCoverings := X.standardSeedCoverings τ
  pretopology := X.standardPretopology τ
  specification := X.standardSite_specification τ

/-- Restricting a chosen fppf site does not change its carrier. -/
theorem standardSite_carrier
    (X : ChosenBigSite.{u, v} Scheme.fppfPrecoverage) (τ : StandardTopology) :
    (X.standardSite τ).carrier = X.carrier := rfl

/-- Restricting a chosen fppf site preserves its selected seed schemes. -/
theorem standardSite_seedSchemes
    (X : ChosenBigSite.{u, v} Scheme.fppfPrecoverage) (τ : StandardTopology) :
    (X.standardSite τ).seedSchemes = X.seedSchemes := rfl

/-- The restricted standard pretopology is contained in the original chosen
fppf pretopology. -/
theorem standardSite_pretopology_le
    (X : ChosenBigSite.{u, v} Scheme.fppfPrecoverage) (τ : StandardTopology) :
    (X.standardSite τ).pretopology ≤ X.pretopology := by
  intro T R hR
  exact hR.1

/-- The Grothendieck topology generated by a restricted standard site is
contained in the topology generated by the original chosen fppf site. -/
theorem standardSite_toGrothendieck_le
    (X : ChosenBigSite.{u, v} Scheme.fppfPrecoverage) (τ : StandardTopology) :
    (X.standardSite τ).toGrothendieck ≤ X.toGrothendieck := by
  letI := X.hasPullbacks
  exact Pretopology.toGrothendieck_mono (C := X.carrier) (X.standardSite_pretopology_le τ)

end ChosenBigSite

end AlgebraicGeometry
