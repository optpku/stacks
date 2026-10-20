module

public import Mathlib.RingTheory.Smooth.AdicCompletion
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Kaehler.Retraction

/-!
# Completions of Formally Smooth Retractions

This leaf records the finite-free conormal form of the formal-power-series
description of the completion of a formally smooth algebra retraction.
-/

@[expose] public section

open scoped TensorProduct

namespace Algebra.FormallySmooth.Retraction

universe u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- If a formally smooth algebra retraction has finite free conormal module,
its kernel-adic completion is a finite-variable formal power series algebra. -/
@[stacks 05D5 "formal smooth retraction completion"]
theorem exists_adicCompletion_equiv_mvPowerSeries
    [Algebra.FormallySmooth R S] (sigma : S →ₐ[R] R)
    [Module.Finite R (RingHom.ker sigma).Cotangent]
    [Module.Free R (RingHom.ker sigma).Cotangent] :
    ∃ d : ℕ,
      Nonempty ((AdicCompletion (RingHom.ker sigma) S) ≃ₐ[R] MvPowerSeries (Fin d) R) := sorry

end Algebra.FormallySmooth.Retraction
