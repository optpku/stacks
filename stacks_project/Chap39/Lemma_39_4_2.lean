/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupScheme

universe u

/-
Lemma 39.4.2: A group scheme over S acquires the canonically induced
group-scheme structure after pullback along any morphism S' ⟶ S.
-/
@[stacks 022T] #check (AlgebraicGeometry.GroupScheme.baseChange_X :
  ∀ {S T : AlgebraicGeometry.Scheme.{u}} (G : AlgebraicGeometry.GroupScheme S)
    (f : T ⟶ S), (AlgebraicGeometry.GroupScheme.baseChange G f).X =
      (CategoryTheory.Over.pullback f).obj G.X)
