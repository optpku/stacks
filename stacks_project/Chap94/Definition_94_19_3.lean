/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.BaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Definition 94.19.3: let `Sch_fppf` be a big fppf site, and let `g : S ⟶ S'` be
a morphism of this site. If `X'` is an algebraic stack over `S'`, then the
change of base of `X'` is the algebraic stack `X'_S` over `S` given by
`AlgebraicStack.baseChange g X'`. Its underlying category is the 2-fibre
product `(Sch/S)_fppf ×_{(Sch/S')_fppf} X'`, with structure morphism the first
projection to `(Sch/S)_fppf`. -/
@[stacks 04X7] #check (AlgebraicGeometry.AlgebraicStack.baseChange :
  ∀ {S S' : Scheme.{u}} (g : S ⟶ S') (X' : GroupoidsOver S') [AlgebraicStack X'],
    GroupoidsOver S)
