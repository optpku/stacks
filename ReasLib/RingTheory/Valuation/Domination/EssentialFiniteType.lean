module

public import Mathlib.RingTheory.EssentialFiniteness
public import ReasLib.FieldTheory.Transcendence.FiniteType
public import ReasLib.RingTheory.MvPolynomial.FractionRing
public import ReasLib.RingTheory.Localization.AtPrime.FractionRing
public import ReasLib.RingTheory.Localization.AtPrime.LocalHom
public import ReasLib.RingTheory.Localization.FractionRing.EssentialFiniteness
public import ReasLib.RingTheory.Localization.FractionRing.FiniteDimensional
public import ReasLib.RingTheory.Valuation.Domination.FiniteExtension
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Discrete valuation domination in essentially finite-type extensions

This leaf is the finite-transcendence-degree extension of the finite-dimensional
domination owner.  The polynomial presentation, closed-point localization, and
finite-dimensionality transport remain proof-side infrastructure; the public
statement exposes only the neutral field-extension hypotheses and the canonical
domination relation.
-/

@[expose] public section

universe u v w

namespace ValuationSubring

variable {R : Type u} {K : Type v} {L : Type w}
variable [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]

/-- Tag `00PH`: an essentially finite-type field extension of the fraction field of a
non-field Noetherian local domain admits a discrete valuation subring dominating
the image of the base.  This is the reusable existence owner; chapter files keep
only source-facing bridges to this declaration. -/
@[stacks 00PH "DVR domination in an essentially finite-type extension"]
theorem exists_dvr_dominating_of_not_isField_of_essFiniteType
    [Algebra.EssFiniteType K L] (hR : ¬ IsField R) :
    ∃ V : ValuationSubring L,
      IsDiscreteValuationRing V ∧
        LocalSubring.range (algebraMap R L) ≤ V.toLocalSubring := sorry

end ValuationSubring
