/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.DoldKan.AlternatingFaceMapComplex
public import ReasLib.AlgebraicTopology.SimplicialObject.EilenbergMacLane.Extension.Index
public import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 0196

# Acyclicity of the Eilenberg--MacLane extension

This leaf applies the alternating-face-map complex to the reusable extension object.  The base
extension module remains independent of this later homological consequence.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology HomologicalComplex
open scoped Simplicial DoldKan

universe v u

namespace CategoryTheory.SimplicialObject.eilenbergMacLane.extension

variable {𝒜 : Type u} [Category.{v} 𝒜] [Preadditive 𝒜]
  [HasZeroObject 𝒜] [HasFiniteCoproducts 𝒜]

/-- The alternating face map complex of the Eilenberg-MacLane extension object is acyclic. -/
@[stacks 0196 "acyclic Eilenberg-MacLane extension"]
theorem object.acyclic (A : 𝒜) (k : ℕ) :
    K[object A k].Acyclic := sorry

end CategoryTheory.SimplicialObject.eilenbergMacLane.extension
