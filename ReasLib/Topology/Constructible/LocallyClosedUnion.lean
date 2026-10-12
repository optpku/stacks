/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Constructible
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Topology.Constructible.FiniteUnion
public import ReasLib.Topology.LocallyClosed.LocalUnion

/-!
# Constructible Locally Closed Unions

Conversions from constructible predicates to the lighter locally-closed-union
predicates belong here so the basic locally-closed API stays independent of
constructibility.
-/

@[expose] public section

universe u

open Set TopologicalSpace Topology

variable {X : Type u} [TopologicalSpace X]

/-- A constructible subset is a union of locally closed subsets. -/
theorem Topology.IsConstructible.isUnionOfLocallyClosed {T : Set X}
    (hT : IsConstructible T) : IsUnionOfLocallyClosed T := sorry

/-- A locally constructible subset is locally a union of locally closed
subsets. -/
theorem Topology.IsLocallyConstructible.isLocallyUnionOfLocallyClosed {T : Set X}
    (hT : IsLocallyConstructible T) : IsLocallyUnionOfLocallyClosed T := sorry

/-- A constructible subset is locally a union of locally closed subsets. -/
theorem Topology.IsConstructible.isLocallyUnionOfLocallyClosed {T : Set X}
    (hT : IsConstructible T) : IsLocallyUnionOfLocallyClosed T := sorry
