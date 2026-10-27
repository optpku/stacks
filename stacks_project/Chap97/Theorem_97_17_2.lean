/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Algebraic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.SmallAction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.SmallModuli
import StacksCheckRecall
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap94.Definition_94_16_5_Quotient
public import stacks_project.Chap94.Remark_94_16_3_Flat
public import stacks_project.Chap94.Remark_94_16_3_LocallyOfFinitePresentation

/-!
# Quotient stacks of flat locally finitely presented groupoids

The quotient stack `[U / R]` associated to a groupoid in algebraic spaces
whose source and target are flat and locally of finite presentation is an
algebraic stack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/- Theorem 97.17.2: the quotient stack of a flat, locally finitely presented
groupoid in algebraic spaces over the base is an algebraic stack. -/
@[stacks 06FI] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.isAlgebraicStack_quotientStack_of_flat :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
      (h_flat : Flat G) (h_lfp : LocallyOfFinitePresentation G),
      AlgebraicStack (SmallQuotient.quotientStack G))

end AlgebraicGeometry.GroupoidAlgebraicSpace
