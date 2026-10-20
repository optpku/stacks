/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.HomFinite
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 41.6.4: Let `S` be a Noetherian scheme. Let `X ⟶ S` be a quasi-compact
unramified morphism. Let `Y ⟶ S` be a morphism with `Y` Noetherian. Then the type of
`S`-morphisms from `Y` to `X` is finite. -/
@[stacks 0AKI] #check
  (AlgebraicGeometry.Unramified.homFinite :
    ∀ {S : Scheme.{u}} [IsNoetherian S] (X Y : Over S) [QuasiCompact X.hom]
      [Unramified X.hom] [IsNoetherian Y.left], Finite (Y ⟶ X))
