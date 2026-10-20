module

public import ReasLib.Algebra.Module.Length
public import ReasLib.RingTheory.Ideal.HilbertSamuel
public import ReasLib.RingTheory.Ideal.OfDefinition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Hilbert--Samuel comparison under a change of ideal of definition

@stack 00K7

The core statements use positive naturals as the index and reindexing factor.
This removes the source-level side condition `1 ≤ n` from downstream uses while
retaining an eventual `ℕ` form for filter arguments.
-/

@[expose] public section

open Filter

universe u v

namespace Ideal.HilbertSamuel

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Positive-index Hilbert--Samuel `χ` values for two ideals of definition are
ordered after a fixed positive linear reindexing. -/
@[stacks 00K7 "reindexed Hilbert-Samuel chi comparison"]
theorem exists_reindex_chi_le {I J : Ideal R}
    (hI : I.IsIdealOfDefinition) (hJ : J.IsIdealOfDefinition) :
    ∃ a : ℕ+, ∀ n : ℕ+,
      I.hilbertSamuelChi M (n : ℕ) ≤
        J.hilbertSamuelChi M ((a : ℕ) * (n : ℕ)) := sorry

/-- Filter-level form of `exists_reindex_chi_le`, suitable for eventual
polynomial comparison. -/
@[stacks 00K7 "eventual reindexed Hilbert-Samuel chi comparison"]
theorem exists_eventually_reindex_chi_le {I J : Ideal R}
    (hI : I.IsIdealOfDefinition) (hJ : J.IsIdealOfDefinition) :
    ∃ a : ℕ+, ∀ᶠ n : ℕ in atTop,
      I.hilbertSamuelChi M n ≤ J.hilbertSamuelChi M ((a : ℕ) * n) := sorry

end Ideal.HilbertSamuel
