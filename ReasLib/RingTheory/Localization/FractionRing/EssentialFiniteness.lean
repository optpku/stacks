module

public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Essential finite type after fraction-field base change

This leaf owns the neutral localization transport used when a chosen fraction-field
model is replaced by the canonical `FractionRing` model.  It does not assume that
the rings are domains or fields: those hypotheses belong to the fraction-field
model supplied by the caller, while essential finite type itself is a ring-level
property.
-/

@[expose] public section

universe u v w

namespace Algebra.EssFiniteType

variable {R : Type u} {K : Type v} {L : Type w}
variable [CommRing R] [CommRing K] [CommRing L]
variable [Algebra R K] [IsFractionRing R K]
variable [Algebra K L] [Algebra R L] [Algebra (FractionRing R) L]
variable [IsScalarTower R K L] [IsScalarTower R (FractionRing R) L]
variable [Algebra.EssFiniteType K L]

/-- The essentially finite-type property descends from a chosen fraction-field model
to the canonical `FractionRing` model by localization composition. -/
@[stacks 00PH "essential finite type after fraction-ring base change"]
theorem of_fractionRing : Algebra.EssFiniteType (FractionRing R) L := sorry

end Algebra.EssFiniteType
