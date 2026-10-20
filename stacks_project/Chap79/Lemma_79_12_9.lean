/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePart.BaseChange
import StacksCheckRecall

/-! # Fibre products of finite-part sheaves -/

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits

universe u

/- Lemma 79.12.9: Finite-part sheaves commute with base change. -/
@[stacks 04QF] #check (AlgebraicGeometry.AlgebraicSpace.finitePart_isPullback :
  ∀ {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
    {fX : X ⟶ Y} {fX' : X' ⟶ Y'} {pX : X' ⟶ X} {pY : Y' ⟶ Y}
    (h : IsPullback pX fX' fX pY),
    IsPullback (finitePartMap h) (finitePartTo fX') (finitePartTo fX)
      ((toFppfSheaf S).map pY))
