module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.FormalFiber.PRing
public import ReasLib.RingTheory.FormalFiber.FieldProperty.Laws

@[expose] public section

/-!
# Detecting P-rings at maximal ideals

The maximal-local criterion uses exactly regular-fiber ascent and faithfully flat descent.  It is
kept separate from the definition of a `P`-ring so consumers do not acquire unused law assumptions.

@stack 0BIU
-/

universe u

namespace IsPRing

/-- For a Noetherian ring and a property stable under regular ascent and faithfully flat descent,
the `P`-ring condition is detected by formal fibers at maximal localizations. -/
@[stacks 0BIU "maximal-local criterion for P-rings"]
theorem iff_forall_maximal_holdsOnFormalFibers
    (P : FieldAlgebraProperty.{u, u}) [P.RegularFiberAscent] [P.FaithfullyFlatDescent]
    (R : Type u) [CommRing R] [IsNoetherianRing R] :
    IsPRing P R ↔
      ∀ m : MaximalSpectrum R,
        P.HoldsOnFormalFibers (Localization.AtPrime m.asIdeal) := sorry

/-- At a maximal ideal, the localized ring is a `P`-ring exactly when its own formal fibers
have `P`, provided `P` has the ascent and descent laws used by the maximal-local criterion. -/
@[stacks 0BIU "maximal localization criterion for P-rings"]
theorem localizationAtMaximal_iff_holdsOnFormalFibers
    (P : FieldAlgebraProperty.{u, u}) [P.RegularFiberAscent] [P.FaithfullyFlatDescent]
    (R : Type u) [CommRing R] [IsNoetherianRing R] (m : MaximalSpectrum R) :
    IsPRing P (Localization.AtPrime m.asIdeal) ↔
      P.HoldsOnFormalFibers (Localization.AtPrime m.asIdeal) := sorry

end IsPRing
