/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.QuotSMulTop
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.LocalProperties.Semilocal
public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite length of principal module quotients

For an `R`-submodule of a finite-dimensional vector space over the fraction
field of `R`, principal `QuotSMulTop` quotients have finite length, with a
sharper length bound when `R` is local.
-/

@[expose] public section

universe u v w

namespace QuotSMulTop

variable {R : Type u} {K : Type v} {V : Type w}
variable [CommRing R] [IsDomain R] [IsNoetherianRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
variable [FiniteDimensional K V]

include K

section

variable [Ring.KrullDimLE 1 R]

/-- A nonzero principal quotient of an `R`-submodule in a finite-dimensional
fraction-field vector space has finite `R`-length. -/
@[stacks 00PF "finite length of a principal quotient in finite dimension"]
theorem isFiniteLength_of_nonzero
    (M : Submodule R V) {x : R} (hx : x ≠ 0) :
    IsFiniteLength R (QuotSMulTop x M) := sorry

/- Proof strategy: use `isFiniteLength_quotient_span_singleton` for the scalar quotient, derive
`IsArtinianRing` for the principal quotient with `isArtinianRing_iff_isFiniteLength`, and apply
`Module.Finite.of_localized_maximal` to its maximal localizations.  Transport the local
finite-dimensional coordinate reduction through `LinearEquiv.ofFinrankEq` and
`QuotSMulTop.congr`; `Module.length_ne_top_iff` closes the Noetherian and Artinian finite-length
step.  `IsNoetherianRing R`, `Ring.KrullDimLE 1 R`, and `IsFractionRing R K` provide the local
finite-length and fraction-field hypotheses. -/

variable [IsLocalRing R]

/-- In the local one-dimensional case, the length of a principal quotient
is bounded by the ambient vector-space dimension times the length of the scalar quotient. -/
@[stacks 00PE "finite-dimensional principal quotient length bound"]
theorem length_le_finrank_mul_length_quotient_span_singleton
    (M : Submodule R V) {x : R} :
    Module.length R (QuotSMulTop x M) ≤
      Module.finrank K V * Module.length R (R ⧸ Ideal.span ({x} : Set R)) := sorry

/- Proof strategy: choose a finite-dimensional coordinate model with `LinearEquiv.ofFinrankEq`,
use `QuotSMulTop.congr` and `Module.length_pi_of_fintype` for the free case, and clear
denominators with `Module.length_eq_of_surjective`; `isFiniteLength_quotient_span_singleton`
supplies the principal scalar length, while `Ring.KrullDimLE 1 R` and `IsLocalRing R` discharge
the one-dimensional local branches. -/

end


/-- The dimension-one form of `QuotSMulTop.isFiniteLength_of_nonzero`, with the
Krull-dimension bound supplied as an equality. -/
@[stacks 00PF "ring Krull dimension one specialization"]
theorem isFiniteLength_of_ringKrullDim_eq_one
    (hdim : ringKrullDim R = 1) (M : Submodule R V) {x : R} (hx : x ≠ 0) :
    IsFiniteLength R (QuotSMulTop x M) := by
  -- Local instance justification (proof-local temporary data): the dimension equality supplies
  -- the dimension-bound class needed for this application.
  letI : Ring.KrullDimLE 1 R := (Ring.krullDimLE_iff).2 (hdim.le.trans_eq rfl)
  exact isFiniteLength_of_nonzero (R := R) (K := K) (V := V) M hx

end QuotSMulTop
