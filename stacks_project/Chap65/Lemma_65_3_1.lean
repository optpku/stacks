/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Yoneda

@[expose] public section

universe u

open CategoryTheory Limits

/- Lemma 65.3.1 -/
@[stacks 02W9] #check (AlgebraicGeometry.yonedaMap_relativelyRepresentable :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : CategoryTheory.Over S} (f : X ⟶ Y),
    CategoryTheory.yoneda.relativelyRepresentable (CategoryTheory.yoneda.map f))
