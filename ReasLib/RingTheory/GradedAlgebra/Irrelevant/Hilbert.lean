/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.GradedAlgebra.Irrelevant.Dimension
public import ReasLib.RingTheory.GradedAlgebra.DegreeOne
public import ReasLib.RingTheory.Ideal.HilbertSamuel.Dimension
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Hilbert functions at the irrelevant closed point

The local Hilbert--Samuel function is first compared with the cardinal rank of
each homogeneous piece.  Finite-dimensional and polynomial formulations are
separate companions, so the core statement does not carry unnecessary
finite-type assumptions.
-/

open scoped HomogeneousIdeal
open IsLocalRing

universe u v

namespace HomogeneousIdeal.Irrelevant

variable {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]
variable (𝒜 : ℕ → Submodule k S) [GradedAlgebra 𝒜]

/-- For a degree-one generated graded algebra, the Hilbert--Samuel function
of the irrelevant local ring is the cardinal rank of the corresponding
homogeneous piece. -/
@[stacks 00P6 "(4), irrelevant-local Hilbert function by rank"]
theorem hilbertSamuelPhi_eq_rank
    (hgenerated : GradedAlgebra.DegreeOneGenerated 𝒜)
    (zeroEquiv : k ≃ₐ[k] 𝒜 0) (d : ℕ) :
    Ideal.hilbertSamuelPhi
        (maximalIdeal (LocalRing 𝒜 zeroEquiv))
        (LocalRing 𝒜 zeroEquiv) d =
      (Module.rank k (𝒜 d)).toENat := sorry

/-- The finite-dimensional form of the irrelevant-local Hilbert-function
comparison. -/
@[stacks 00P6 "(4), irrelevant-local Hilbert function by finrank"]
theorem hilbertSamuelPhi_eq_finrank
    (hgenerated : GradedAlgebra.DegreeOneGenerated 𝒜)
    (zeroEquiv : k ≃ₐ[k] 𝒜 0) (d : ℕ)
    [Module.Finite k (𝒜 d)] :
    Ideal.hilbertSamuelPhi
        (maximalIdeal (LocalRing 𝒜 zeroEquiv))
        (LocalRing 𝒜 zeroEquiv) d =
      (Module.finrank k (𝒜 d) : ℕ∞) := sorry

/-- Finite type over the degree-zero piece supplies the finite-dimensional
homogeneous pieces needed by the source-facing `finrank` formula. -/
@[stacks 00P6 "(4), graded and local Hilbert functions"]
theorem hilbertSamuelPhi_eq_finrank_of_finiteType
    [Algebra.FiniteType (𝒜 0) S]
    (hgenerated : GradedAlgebra.DegreeOneGenerated 𝒜)
    (zeroEquiv : k ≃ₐ[k] 𝒜 0) (d : ℕ) :
    Ideal.hilbertSamuelPhi
        (maximalIdeal (LocalRing 𝒜 zeroEquiv))
        (LocalRing 𝒜 zeroEquiv) d =
      (Module.finrank k (𝒜 d) : ℕ∞) := sorry

/-- An eventual polynomial for the graded Hilbert function computes the
global Krull dimension of a standard graded algebra. -/
@[stacks 00P6 "(3), dimension from the graded Hilbert polynomial"]
theorem ringKrullDim_eq_degree_succ_of_eventuallyEq_finrank
    [Algebra.FiniteType (𝒜 0) S]
    (hgenerated : GradedAlgebra.DegreeOneGenerated 𝒜)
    (zeroEquiv : k ≃ₐ[k] 𝒜 0) (P : Polynomial ℚ)
    (hP : P.EventuallyEqNat (fun d ↦ (Module.finrank k (𝒜 d) : ℚ))) :
    ringKrullDim S = P.degree.succ := sorry

end HomogeneousIdeal.Irrelevant
