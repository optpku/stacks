/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Sober
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Kolmogorov Quotients from Finite Spans

An open quotient of a quasi-sober `T₀` space is Kolmogorov when its fibers are
represented by a span of finite-fiber generalizing maps.
-/

@[expose] public section

universe u v w

open Set

variable {R : Type u} {U : Type v} {X : Type w}
variable [TopologicalSpace R] [TopologicalSpace U] [TopologicalSpace X]
variable [T0Space U] [QuasiSober U]
variable {s t : R → U} {π : U → X}

namespace IsOpenQuotientMap

/-- Lemma 5.19.8: an open quotient whose fibers are represented by a span of
finite-fiber generalizing maps from a quasi-sober `T₀` space has `T₀` target. -/
@[stacks 06NA]
theorem t0Space_of_finiteFibers_of_spanEq
    (hπ : IsOpenQuotientMap π)
    (hs_cont : Continuous s) (ht_cont : Continuous t)
    (hs_finite : ∀ u : U, (s ⁻¹' ({u} : Set U)).Finite)
    (ht_finite : ∀ u : U, (t ⁻¹' ({u} : Set U)).Finite)
    (hs_gen : GeneralizingMap s) (ht_gen : GeneralizingMap t)
    (hspan : ∀ u v : U, π u = π v ↔ ∃ r : R, t r = u ∧ s r = v) :
    T0Space X := sorry

end IsOpenQuotientMap
