/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Dualizing.Basic
import StacksCheckRecall

universe u

/- Definition 86.2.2: let `S` be a scheme. Let `X` be a locally Noetherian algebraic space
over `S`. An object `K` of `D_QCoh(𝒪_X)` is called a dualizing complex if `K` satisfies
the equivalent conditions of Lemma 86.2.1. -/
@[stacks 0E4Z] #check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.IsDualizingComplex :
  {S : AlgebraicGeometry.Scheme.{u}} →
    {X : AlgebraicGeometry.AlgebraicSpace S} →
      [AlgebraicGeometry.AlgebraicSpace.IsLocallyNoetherian X] →
        AlgebraicGeometry.AlgebraicSpace.DerivedQCoh X → Prop)
