/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.ValuativeCriterion
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 108.5.3: if `f : X ⟶ B` is proper and of finite presentation and
`F` is a quasi-coherent finite-type module on `X`, then `quot f F` satisfies
the existence part of the valuative criterion. -/
@[stacks 0DM4] #check (AlgebraicGeometry.AlgebraicSpace.Quot.instExistence :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
    [FinitePresentation f] [Proper f] (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType],
    SchemeOver.ValuativeCriterion.Existence (Quot.quot f F))
