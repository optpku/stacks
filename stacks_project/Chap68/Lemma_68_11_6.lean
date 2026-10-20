/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleNeighborhood.Cofiltered
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 68.11.6: Let `S` be a scheme. Let `X` be a decent algebraic space over `S`. Let `x` be
a point of `X`. The category of elementary étale neighbourhoods of `(X, x)` is cofiltered. -/
@[stacks 0BGV] #check
  (AlgebraicGeometry.AlgebraicSpace.EtaleNeighborhood.Elementary.instIsCofiltered :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X] (x : Points X),
      IsCofiltered (EtaleNeighborhood.Elementary X x))
