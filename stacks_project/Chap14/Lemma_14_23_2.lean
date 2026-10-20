/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.EilenbergMacLane.Extension.Acyclic
import StacksCheckRecall

@[expose] public section

/-!
# Source-facing bridge for Lemma 14.23.2

@stack 0196

Acyclicity of the alternating face map complex belongs to the reusable Eilenberg-MacLane
extension owner.
-/

open CategoryTheory
open scoped Simplicial DoldKan

noncomputable section

universe v u

namespace CategoryTheory.SimplicialObject.eilenbergMacLane

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable (A : 𝒜) (k : ℕ)

/- Lemma 14.23.2: the alternating face map complex of the extension object is acyclic. -/
@[stacks 0196]
#check (extension.object.acyclic A k : K[extension.object A k].Acyclic)

#check (ChainComplex.disk.acyclic A k)

end CategoryTheory.SimplicialObject.eilenbergMacLane
