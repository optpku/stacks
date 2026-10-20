/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
public import Mathlib.RingTheory.Valuation.LocalSubring
public import ReasLib.RingTheory.Localization.FractionRing.IntegralClosure.AtPrime
public import ReasLib.RingTheory.Localization.FractionRing.OneDimensionalOverring
public import ReasLib.RingTheory.Valuation.Domination
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Discrete valuation domination in finite field extensions

This leaf exposes the finite-dimensional existence theorem at the valuation-subring
boundary.  The intermediate one-dimensional overring and the normalization prime
are proof infrastructure, not public data; callers receive only the dominating
discrete valuation subring and the canonical `LocalSubring.range` inequality.
-/

@[expose] public section

universe u v w

namespace ValuationSubring

variable {R : Type u} {K : Type v} {L : Type w}
variable [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]

/-- Tag `00PH`: a finite-dimensional field extension of the fraction field of a
non-field Noetherian local domain admits a discrete valuation subring dominating
the image of the base.  The theorem is intentionally stated at the bundled
`ValuationSubring`/`LocalSubring` interface so it composes with both the generic
valuation-overring API and `exists_ofDvr_dominating`. -/
@[stacks 00PH "DVR domination in a finite-dimensional fraction-field extension"]
theorem exists_dvr_dominating_of_not_isField_of_finiteDimensional
    [FiniteDimensional K L] (hR : ¬ IsField R) :
    ∃ V : ValuationSubring L,
      IsDiscreteValuationRing V ∧
        LocalSubring.range (algebraMap R L) ≤ V.toLocalSubring := sorry

end ValuationSubring
