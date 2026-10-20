module

public import ReasLib.RingTheory.GradedAlgebra.Irrelevant
public import ReasLib.RingTheory.KrullDimension.FiniteType.Local
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Dimension at the irrelevant closed point

The global-to-local comparison is separated from Hilbert functions.  Its only
geometric input is that every minimal prime lies below the irrelevant ideal.
-/

open scoped HomogeneousIdeal
open TopologicalSpace

universe u v

namespace HomogeneousIdeal.Irrelevant

variable {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]
variable (𝒜 : ℕ → Submodule k S) [GradedAlgebra 𝒜]

/-- The local ring of a graded algebra at its irrelevant closed point. -/
@[stacks 00P6 "local ring at the irrelevant ideal"]
abbrev LocalRing (zeroEquiv : k ≃ₐ[k] 𝒜 0) :=
  Localization.AtPrime
    (HomogeneousIdeal.irrelevantMaximalSpectrum 𝒜 zeroEquiv).asIdeal

variable [Algebra.FiniteType (𝒜 0) S]

/-- The local topological dimension at the irrelevant closed point equals the
global Krull dimension. -/
@[stacks 00P6 "(3), dimension at the irrelevant closed point"]
theorem ringKrullDim_eq_topologicalKrullDimAt
    (zeroEquiv : k ≃ₐ[k] 𝒜 0) :
    ringKrullDim S =
      topologicalKrullDimAt
        (HomogeneousIdeal.irrelevantMaximalSpectrum 𝒜 zeroEquiv).toPrimeSpectrum := sorry

/-- Localization at the irrelevant closed point preserves Krull dimension. -/
@[stacks 00P6 "(3), dimension of the irrelevant local ring"]
theorem ringKrullDim_eq_localRing (zeroEquiv : k ≃ₐ[k] 𝒜 0) :
    ringKrullDim S = ringKrullDim (LocalRing 𝒜 zeroEquiv) := sorry

end HomogeneousIdeal.Irrelevant
