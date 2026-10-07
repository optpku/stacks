module

public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# One-dimensional local overrings in a fraction field

This leaf owns the neutral intermediate-overring existence statement used by finite
valuation-domination arguments.  The output records only the local, dimension-one,
essentially-finite-type structure; a later owner may use it to build a normalization,
but no normalization or valuation witness is part of this API.
-/

@[expose] public section

universe u v

namespace FractionRing

variable {R : Type u} {K : Type v}
variable [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]

/-- Tag `00P8`: a non-field Noetherian local domain has a one-dimensional local
essentially-finite-type overring inside its chosen fraction field.  The returned
subalgebra is the canonical intermediate object; locality, dimension, and essential
finite type are separate fields so downstream normalization arguments can consume
only the property they need. -/
@[stacks 00P8 "one-dimensional local overring in a fraction field"]
theorem exists_local_dimOne_overring_of_not_isField
    (hR : ¬ IsField R) :
    ∃ A : Subalgebra R K,
      ringKrullDim A = 1 ∧
        IsLocalRing A ∧
        IsLocalHom (algebraMap R A) ∧
        Algebra.EssFiniteType R A := sorry

end FractionRing
