/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap96.Definition_96_6_1_StructureSheaf
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Definition 96.6.1: let `p : X ⟶ (Sch/S)_fppf` be a category fibred in
groupoids. The structure sheaf of `X` is the sheaf of rings
`𝒪_X = p⁻¹ 𝒪`. -/
@[stacks 06TV] #check
  (AlgebraicGeometry.GroupoidsOver.structureSheaf :
    {S : Scheme.{u}} → (X : GroupoidsOver S) →
      Sheaf (GroupoidsOver.fppfTopology X) RingCat.{u})

/- For an object `x` of `X` lying over `U`, `𝒪_X(x) = Γ(U, 𝒪_U)`. -/
#check GroupoidsOver.structureSheaf_obj
