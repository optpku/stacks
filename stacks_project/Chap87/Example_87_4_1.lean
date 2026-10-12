/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.Topology.Algebra.LinearTopology
import ReasLib.Topology.Algebra.Module.PowerSeriesDirectSum

/-!
# Example 87.4.1

Continuity of addition on a linearly topologized module is automatic. Continuity of
scalar multiplication unpacks as a pointwise absorption condition on open ideals, which
need not upgrade to uniform absorption. Continuous maps of linearly topologized rings
preserve open-ideal containment.
-/

universe u v

open scoped Pointwise

/- Example 87.4.1 (1): If `M` is a linearly topologized `R`-module, then addition is continuous. -/
@[stacks 0AMR] #check (IsLinearTopology.continuousAdd :
    ∀ {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
      [TopologicalSpace M] [IsLinearTopology R M] [ContinuousConstVAdd M M],
      Continuous fun p : M × M ↦ p.1 + p.2)

/- Example 87.4.1 (2): Continuity of scalar multiplication is the coset-neighbourhood
criterion on open ideals and open submodules. -/
@[stacks 0AMR] #check (IsLinearTopology.continuousSMul_iff_exists_vadd_smul_subset :
    ∀ {R : Type u} {M : Type v} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R] [AddCommGroup M] [Module R M] [TopologicalSpace M]
      [IsTopologicalAddGroup M] [IsLinearTopology R M],
      Continuous (fun p : R × M ↦ p.1 • p.2) ↔
        ∀ (f : R) (x : M) (N : Submodule R M), IsOpen (N : Set M) →
          ∃ (I : Ideal R) (N' : Submodule R M),
            IsOpen (I : Set R) ∧ IsOpen (N' : Set M) ∧
              (f +ᵥ (I : Set R)) • (x +ᵥ (N' : Set M)) ⊆ (f • x) +ᵥ (N : Set M))

/- Example 87.4.1 (3): Continuity of scalar multiplication is equivalent to pointwise ideal
absorption into every open submodule. -/
@[stacks 0AMR] #check (IsLinearTopology.continuousSMul_iff_exists_ideal_smul_mem :
    ∀ {R : Type u} {M : Type v} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
      [IsLinearTopology R R] [AddCommGroup M] [Module R M] [TopologicalSpace M]
      [IsTopologicalAddGroup M] [IsLinearTopology R M],
      Continuous (fun p : R × M ↦ p.1 • p.2) ↔
        ∀ (x : M) (N : Submodule R M), IsOpen (N : Set M) →
          ∃ I : Ideal R, IsOpen (I : Set R) ∧ ∀ r ∈ I, r • x ∈ N)

/- Example 87.4.1 (4): The weighted power-series direct sum is a linearly topologized module
with continuous scalar multiplication. -/
@[stacks 0AMR] #check (IsLinearTopology.PowerSeriesDirectSum.continuousSMul :
    ∀ {k : Type u} [Field k] [TopologicalSpace (PowerSeries k)]
      [IsTopologicalRing (PowerSeries k)] (h_adic : IsAdic (IsLinearTopology.PowerSeriesDirectSum.xIdeal k)),
      Continuous fun p : PowerSeries k × IsLinearTopology.PowerSeriesDirectSum.Module k ↦
        p.1 • p.2)

/- Example 87.4.1 (5): Uniform absorption by powers of `X` fails for every weighted index. -/
@[stacks 0AMR] #check (IsLinearTopology.PowerSeriesDirectSum.not_forall_exists_pow_smul_top :
    ∀ {k : Type u} [Field k],
      ¬ ∀ m : ℕ, ∃ n : ℕ,
        IsLinearTopology.PowerSeriesDirectSum.xIdeal k ^ n •
            (⊤ : Submodule (PowerSeries k) (IsLinearTopology.PowerSeriesDirectSum.Module k)) ≤
          IsLinearTopology.PowerSeriesDirectSum.openSubmodule k m)

/- Example 87.4.1 (6): A continuous map of linearly topologized rings has an open ideal whose
image is contained in every prescribed open ideal. -/
@[stacks 0AMR] #check (IsLinearTopology.exists_open_ideal_map_le :
    ∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] [TopologicalSpace R]
      [TopologicalSpace S] [IsTopologicalRing R] [IsTopologicalRing S] [IsLinearTopology R R]
      [IsLinearTopology S S] (φ : R →+* S) (hφ : Continuous φ) (J : Ideal S)
      (hJ : IsOpen (J : Set S)),
      ∃ I : Ideal R, IsOpen (I : Set R) ∧ I.map φ ≤ J)
