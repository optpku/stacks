/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.WeakDimension.One
import Mathlib.Tactic.CrossRefAttribute

/-!
# Weak dimension of products

This leaf owns the weak-dimension bound for arbitrary dependent products of Bezout domains.
Valuation rings are a specialization through Mathlib's canonical `ValuationRing` to `IsBezout`
instance, so downstream files do not need to install a temporary family of instances.

@stack 092T
-/

@[expose] public section

universe u v

namespace HasWeakDimensionLE

variable {J : Type u} {A : J → Type v}
variable [∀ j, CommRing (A j)]

/-- A dependent product of Bezout domains has weak dimension at most one. -/
@[stacks 092T "products of Bezout domains have weak dimension at most one"]
instance piOfIsBezout [∀ j, IsDomain (A j)] [∀ j, IsBezout (A j)] :
    HasWeakDimensionLE ((j : J) → A j) 1 := sorry

end HasWeakDimensionLE
