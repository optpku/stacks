/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.FormalFiber.GRing
public import ReasLib.RingTheory.FormalFiber.Maximal
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Detecting G-rings at maximal ideals

@stack 07PT

The generic maximal-local criterion for `P`-rings specializes to geometric regularity.  This
file exposes both the formal-fiber formulation used in the source and the equivalent formulation
in terms of G-rings at maximal localizations.
-/

universe u

namespace IsGRing

open FieldAlgebraProperty

variable {R : Type u} [CommRing R]

/-- A maximal localization is a G-ring exactly when its formal fibers are geometrically regular. -/
@[stacks 07PT "maximal localization criterion for G-rings"]
theorem localizationAtMaximal_iff_holdsOnFormalFibers
    (R : Type u) [CommRing R] [IsNoetherianRing R] (m : MaximalSpectrum R) :
    IsGRing (Localization.AtPrime m.asIdeal) ↔
      geometricallyRegular.HoldsOnFormalFibers (Localization.AtPrime m.asIdeal) := sorry

/-- A Noetherian ring is a G-ring exactly when every maximal localization has geometrically
regular formal fibers. -/
@[stacks 07PT "maximal-local criterion for G-rings"]
theorem iff_forall_maximal_holdsOnFormalFibers
    (R : Type u) [CommRing R] [IsNoetherianRing R] :
    IsGRing R ↔
      ∀ m : MaximalSpectrum R,
        geometricallyRegular.HoldsOnFormalFibers (Localization.AtPrime m.asIdeal) := sorry

/-- Every maximal localization of a G-ring is a G-ring. -/
@[stacks 07PT "G-rings at maximal localizations"]
theorem localizationAtMaximal
    (hR : IsGRing R) (m : MaximalSpectrum R) :
    IsGRing (Localization.AtPrime m.asIdeal) := sorry

/-- A Noetherian ring whose maximal localizations are G-rings is a G-ring. -/
@[stacks 07PT "G-rings detected at maximal localizations"]
theorem of_localizationsAtMaximal
    [IsNoetherianRing R]
    (hR : ∀ m : MaximalSpectrum R, IsGRing (Localization.AtPrime m.asIdeal)) :
    IsGRing R := sorry

/-- A Noetherian ring is a G-ring exactly when all its maximal localizations are G-rings. -/
@[stacks 07PT "maximal-local G-ring criterion"]
theorem iff_forall_localizationAtMaximal
    (R : Type u) [CommRing R] [IsNoetherianRing R] :
    IsGRing R ↔
      ∀ m : MaximalSpectrum R, IsGRing (Localization.AtPrime m.asIdeal) := sorry

end IsGRing
