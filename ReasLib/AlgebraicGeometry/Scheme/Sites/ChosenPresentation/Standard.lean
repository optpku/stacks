module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Standard
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.Comparison

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
    τ.precoverage ≤ Scheme.fppfPrecoverage := sorry

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
      R ∈ X.seedCoverings T ∧ R ∈ X.standardPrecoverage τ T := sorry

/-- Singleton isomorphisms cover in every restricted standard precoverage. -/
theorem standardPrecoverage_hasIsos
    (X : ChosenBigSite.{u, v} Scheme.fppfPrecoverage) (τ : StandardTopology) :
    ∀ ⦃S T : X.carrier⦄ (f : S ⟶ T) [IsIso f],
      Presieve.singleton f ∈ X.standardPrecoverage τ T := sorry

/-- Restricted standard covering families are stable under the chosen
pullbacks. -/
theorem standardPrecoverage_pullbacks
    (X : ChosenBigSite.{u, v} Scheme.fppfPrecoverage) (τ : StandardTopology) :
    ∀ ⦃S T : X.carrier⦄ (f : S ⟶ T) (R : Presieve T),
      R ∈ X.standardPrecoverage τ T →
        @Presieve.pullbackArrows X.carrier (Cat.str X.carrier) T S f R
          ⟨fun _ => X.hasPullbacks.has_limit _⟩ ∈ X.standardPrecoverage τ S := sorry

/-- Restricted standard covering families are stable under composition. -/
theorem standardPrecoverage_transitive
    (X : ChosenBigSite.{u, v} Scheme.fppfPrecoverage) (τ : StandardTopology) :
    ∀ ⦃T : X.carrier⦄ (R : Presieve T)
      (Rᵢ : ∀ ⦃S : X.carrier⦄ (f : S ⟶ T), R f → Presieve S),
      R ∈ X.standardPrecoverage τ T →
        (∀ ⦃S : X.carrier⦄ (f : S ⟶ T) (h : R f),
          Rᵢ f h ∈ X.standardPrecoverage τ S) →
            R.bind Rᵢ ∈ X.standardPrecoverage τ T := sorry

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
    (X.standardSite τ).carrier = X.carrier := sorry

/-- Restricting a chosen fppf site preserves its selected seed schemes. -/
theorem standardSite_seedSchemes
    (X : ChosenBigSite.{u, v} Scheme.fppfPrecoverage) (τ : StandardTopology) :
    (X.standardSite τ).seedSchemes = X.seedSchemes := sorry

/-- The restricted standard pretopology is contained in the original chosen
fppf pretopology. -/
theorem standardSite_pretopology_le
    (X : ChosenBigSite.{u, v} Scheme.fppfPrecoverage) (τ : StandardTopology) :
    (X.standardSite τ).pretopology ≤ X.pretopology := sorry

/-- The Grothendieck topology generated by a restricted standard site is
contained in the topology generated by the original chosen fppf site. -/
theorem standardSite_toGrothendieck_le
    (X : ChosenBigSite.{u, v} Scheme.fppfPrecoverage) (τ : StandardTopology) :
    (X.standardSite τ).toGrothendieck ≤ X.toGrothendieck := sorry

end ChosenBigSite

end AlgebraicGeometry
