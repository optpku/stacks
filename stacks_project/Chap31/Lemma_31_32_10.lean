/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.GenericPoints

open AlgebraicGeometry
open CategoryTheory

universe u

/- Lemma 31.32.10: a blowup induces a bijection from the generic points of its source to the
generic points of the base outside the support of its center. -/
@[stacks 0BFM] #check
  (AlgebraicGeometry.IsBlowup.bijOn_genericPoints_compl_support :
    ∀ {X X' : Scheme.{u}} (I : X.IdealSheafData) (b : X' ⟶ X) [IsBlowup b I],
      Set.BijOn b
        (genericPoints X')
        (genericPoints X ∩ (I.support : Set X)ᶜ))
