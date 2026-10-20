/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Spaces.Stack
import StacksCheckRecall

/-!
# Lemma 99.13.3

The primed categories `Spaces'_ft` and `Spaces'_{fp, flat, proper}` are stacks
in groupoids over `(Sch/S)_fppf`.
-/

universe u

/- Lemma 99.13.3 (1): finite-type algebraic spaces with cartesian squares as
morphisms form a stack in groupoids for the fppf topology. -/
@[stacks 0D1G]
#check (AlgebraicGeometry.AlgebraicSpace.Spaces.FtGroupoids.instIsStackInGroupoids :
  ∀ S : AlgebraicGeometry.Scheme.{u}, CategoryTheory.IsStack.InGroupoids
    (AlgebraicGeometry.Scheme.fppfTopology.over S)
    (AlgebraicGeometry.AlgebraicSpace.Spaces.pFtGroupoids S))

/- Lemma 99.13.3 (2): the finite-presentation, flat, proper full subcategory
is a stack in groupoids for the fppf topology. -/
@[stacks 0D1G]
#check (AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProperGroupoids.instIsStackInGroupoids :
  ∀ S : AlgebraicGeometry.Scheme.{u}, CategoryTheory.IsStack.InGroupoids
    (AlgebraicGeometry.Scheme.fppfTopology.over S)
    (AlgebraicGeometry.AlgebraicSpace.Spaces.pFpFlatProperGroupoids S))
