/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChangeOfBase
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Definition 65.16.2 (1): let `g : S ⟶ S'` be a morphism of the big fppf site, with
localization functor `j = Over.map g`. If `F'` is an algebraic space over `S'`, then the
base change of `F'` to `S` is the algebraic space `j⁻¹ F'` given by
`AlgebraicSpace.baseChange g F'`. The source denotes this `F'_S`. -/
@[stacks 03I5] #check (AlgebraicGeometry.AlgebraicSpace.baseChange :
  ∀ {S S' : Scheme.{u}}, (S ⟶ S') → AlgebraicSpace S' → AlgebraicSpace S)

/- Definition 65.16.2 (2): if `F` is an algebraic space over `S`, then `F` viewed as an
algebraic space over `S'` is the algebraic space `j_! F` given by
`AlgebraicSpace.extendBase g F`. The source often denotes this `F`; otherwise it writes
`j_! F`. -/
@[stacks 03I5] #check (AlgebraicGeometry.AlgebraicSpace.extendBase :
  ∀ {S S' : Scheme.{u}}, (S ⟶ S') → AlgebraicSpace S → AlgebraicSpace S')
