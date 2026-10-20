/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Sheaves.Pointwise.Product
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] {X : TopCat.{v}}
variable (F : C ⥤ Type v) [IsAlgebraicStructure C F] (A : X → C)

/- Example 6.15.6: if `(C, F)` is a type of algebraic structures and `A : X → C`, then the
pointwise product presheaf `U ↦ ∏ x : U, A x` is a sheaf. -/
@[stacks 007R]
#check TopCat.Presheaf.PointwiseProduct.isSheaf F A
