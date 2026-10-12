/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Constructible
public import ReasLib.Topology.LocallyClosed.FiniteUnion

/-!
# Constructible sets as finite locally closed unions

This bridge separates the constructible-set consequence from the lower-level
finite locally closed union API, so consumers of the latter do not need the
constructible topology machinery.
-/

@[expose] public section

universe u

open Set TopologicalSpace Topology

section

variable {X : Type u} [TopologicalSpace X]

namespace Topology

/-- Any constructible subset is a finite union of locally closed subsets. -/
theorem IsConstructible.isFiniteUnionOfLocallyClosed {E : Set X} (hE : IsConstructible E) :
    IsFiniteUnionOfLocallyClosed E := sorry

end Topology

end
