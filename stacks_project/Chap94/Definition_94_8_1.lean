/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

variable (S : Scheme.{u})

/- Definition 94.8.1: a category fibred in groupoids `X` over `(Sch/S)_fppf` is
representable by an algebraic space over `S` if there exists an algebraic space
`F : AlgebraicSpace S` and an equivalence `X ≌ F.toGroupoids` of categories over
`(Sch/S)_fppf`. -/
@[stacks 04SV] #check (AlgebraicGeometry.IsRepresentableByAlgebraicSpace :
  CategoryTheory.ObjectProperty (AlgebraicGeometry.GroupoidsOver S))
