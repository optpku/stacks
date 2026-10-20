/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.UniversalProperty
import StacksCheckRecall

universe u

/- Lemma 31.32.5 (Universal property blowing up): the blowup of a closed subscheme of `X` is
terminal among schemes over `X` on which the inverse image of the center is an effective Cartier
divisor. -/
@[stacks 0806]
#check
  (AlgebraicGeometry.effectiveCartierPullbackOverCategory.blowupObjectIsTerminal :
    ∀ {X X' : AlgebraicGeometry.Scheme.{u}} (I : X.IdealSheafData)
      (b : X' ⟶ X) [AlgebraicGeometry.IsBlowup b I],
      CategoryTheory.Limits.IsTerminal
        (AlgebraicGeometry.effectiveCartierPullbackOverCategory.blowupObject I b))
