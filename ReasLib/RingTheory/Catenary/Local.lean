/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Catenary.FiniteType

@[expose] public section

/-!
# Local Criteria for Catenarity

Prime-local and maximal-local criteria are exposed independently of their
proof-local comparison constructions.
-/

universe u v

section

variable {R : Type u} [CommRing R]

/-- Catenarity is equivalent to catenarity after localization at every prime ideal, and also
to catenarity after localization at every maximal ideal. -/
@[stacks 0AUN]
theorem isCatenaryRing_localization_tfae :
    List.TFAE
      [ IsCatenaryRing R,
        ∀ p : PrimeSpectrum R, IsCatenaryRing (Localization.AtPrime p.asIdeal),
        ∀ m : MaximalSpectrum R, IsCatenaryRing (Localization.AtPrime m.asIdeal) ] := sorry

/-- A ring is catenary exactly when all of its localizations at prime ideals are catenary. -/
@[stacks 0AUN "catenary prime-local criterion"]
theorem isCatenaryRing_iff_forall_localizationAtPrime :
    IsCatenaryRing R ↔
      ∀ p : PrimeSpectrum R, IsCatenaryRing (Localization.AtPrime p.asIdeal) := sorry

/-- A ring is catenary exactly when all of its localizations at maximal ideals are catenary. -/
@[stacks 0AUN "catenary maximal-local criterion"]
theorem isCatenaryRing_iff_forall_localizationAtMaximal :
    IsCatenaryRing R ↔
      ∀ m : MaximalSpectrum R, IsCatenaryRing (Localization.AtPrime m.asIdeal) := sorry

/-- For a Noetherian ring, universal catenarity is equivalent to universal catenarity after
localization at every prime ideal, and also at every maximal ideal. -/
@[stacks 0AUN]
theorem universallyCatenaryRing_localization_tfae [IsNoetherianRing R] :
    List.TFAE
      [ UniversallyCatenaryRing.{u, v} R,
        ∀ p : PrimeSpectrum R, UniversallyCatenaryRing.{u, v} (Localization.AtPrime p.asIdeal),
        ∀ m : MaximalSpectrum R,
          UniversallyCatenaryRing.{u, v} (Localization.AtPrime m.asIdeal) ] := sorry

/-- A Noetherian ring is universally catenary exactly when all of its localizations at prime
ideals are universally catenary. -/
@[stacks 0AUN "universally catenary prime-local criterion"]
theorem universallyCatenaryRing_iff_forall_localizationAtPrime [IsNoetherianRing R] :
    UniversallyCatenaryRing.{u, v} R ↔
      ∀ p : PrimeSpectrum R,
        UniversallyCatenaryRing.{u, v} (Localization.AtPrime p.asIdeal) := sorry

/-- A Noetherian ring is universally catenary exactly when all of its localizations at maximal
ideals are universally catenary. -/
@[stacks 0AUN "universally catenary maximal-local criterion"]
theorem universallyCatenaryRing_iff_forall_localizationAtMaximal [IsNoetherianRing R] :
    UniversallyCatenaryRing.{u, v} R ↔
      ∀ m : MaximalSpectrum R,
        UniversallyCatenaryRing.{u, v} (Localization.AtPrime m.asIdeal) := sorry

end
