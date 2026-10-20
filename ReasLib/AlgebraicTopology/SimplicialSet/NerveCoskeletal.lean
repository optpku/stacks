/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Coskeleton.Coskeletal
public import Mathlib.AlgebraicTopology.SimplicialSet.Coskeletal
public import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 018E

# One-coskeletality of nerves and standard simplices

The one-coskeletal statement for nerves of thin categories is a reusable owner for the
standard-simplex comparison used throughout simplicial arguments.  The public API is expressed in
the existing `SSet.stdSimplex` namespace; the chapter does not need to expose the pointwise cone
construction used by one particular proof.
-/

@[expose] public section

open CategoryTheory
open scoped Simplicial

universe v u

namespace CategoryTheory.Nerve

/-- A thin category has a one-coskeletal nerve. -/
@[stacks 018E "thin nerves are one-coskeletal"]
instance isCoskeletalOne (C : Type u) [Category.{v} C] [Quiver.IsThin C] :
    SimplicialObject.IsCoskeletal (nerve C) 1 := sorry

end CategoryTheory.Nerve

namespace SSet.stdSimplex

/-- The standard simplex `Δ[n]` is one-coskeletal, by transporting the thin-nerve instance
along `SSet.stdSimplex.isoNerve n`. -/
@[stacks 018E "standard simplex is one-coskeletal"]
instance isCoskeletalOne (n : ℕ) :
    SimplicialObject.IsCoskeletal (Δ[n] : SSet.{u}) 1 := sorry

end SSet.stdSimplex
