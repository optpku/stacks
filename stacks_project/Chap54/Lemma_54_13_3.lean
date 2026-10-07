module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Alteration.LocalConsequences
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.IsAlteration

/- Lemma 54.13.3 (1): a local Noetherian domain admitting an alteration from a regular
integral scheme has a nonzero principal localization that is regular. -/
@[stacks 0BGI] #check (AlgebraicGeometry.IsAlteration.exists_regularLocalization :
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsDomain A]
    (X : Scheme.{u}) [IsIntegral X] (π : X ⟶ Spec (.of A)) [IsAlteration π]
    [Scheme.Regular X], ∃ a : A, a ≠ 0 ∧ IsRegularRing (Localization.Away a))

/- Lemma 54.13.3 (2): a local Noetherian domain admitting an alteration from a regular
integral scheme has finite normalization in its fraction field. -/
@[stacks 0BGI] #check (AlgebraicGeometry.IsAlteration.isN1Ring :
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsDomain A]
    (X : Scheme.{u}) [IsIntegral X] (π : X ⟶ Spec (.of A)) [IsAlteration π]
    [Scheme.Regular X], IsN1Ring A)

/- Lemma 54.13.3 (3): the completion of the normalization along the extended maximal ideal
is a normal ring. -/
@[stacks 0BGI] #check (AlgebraicGeometry.IsAlteration.isNormalRing_adicCompletion :
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsDomain A]
    (X : Scheme.{u}) [IsIntegral X] (π : X ⟶ Spec (.of A)) [IsAlteration π]
    [Scheme.Regular X],
    let B := integralClosure A (FractionRing A)
    IsNormalRing
      (AdicCompletion (Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A)) B))

/- Lemma 54.13.3 (4): the completed local ring of the normalization at every maximal ideal
is normal, and hence is a domain. -/
@[stacks 0BGI] #check (AlgebraicGeometry.IsAlteration.isNormalRing_completedLocalRing :
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsDomain A]
    (X : Scheme.{u}) [IsIntegral X] (π : X ⟶ Spec (.of A)) [IsAlteration π]
    [Scheme.Regular X],
    let B := integralClosure A (FractionRing A)
    ∀ n : MaximalSpectrum B,
      IsNormalRing (PrimeSpectrum.CompletedLocalRing n.toPrimeSpectrum))

/- Lemma 54.13.3 (5): the generic formal fibre of a local Noetherian domain admitting an
alteration from a regular integral scheme is regular. -/
@[stacks 0BGI] #check (AlgebraicGeometry.IsAlteration.isRegularRing_genericFormalFiber :
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsDomain A]
    (X : Scheme.{u}) [IsIntegral X] (π : X ⟶ Spec (.of A)) [IsAlteration π]
    [Scheme.Regular X],
    IsRegularRing
      ((algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)).Fiber
        (⊥ : Ideal A)))

end AlgebraicGeometry.IsAlteration
