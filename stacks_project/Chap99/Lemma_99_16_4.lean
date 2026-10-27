/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Complexes.Groupoids
public import stacks_project.Chap99.Situation_99_16_3

/-!
# Lemma 99.16.4

In Situation 99.16.3 the functor `p : Complexes f ⟶ Over S` is fibred in groupoids.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
universe u

/- Lemma 99.16.4: in Situation 99.16.3, the projection from relatively perfect
complexes with vanishing negative fibre self-Ext to schemes over `S` is fibred
in groupoids. -/
@[stacks 0DLF] #check (AlgebraicGeometry.AlgebraicSpace.Complexes.instIsFiberedInGroupoids :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
    [Proper f] [Flat f] [FinitePresentation f],
    Functor.IsFibered.InGroupoids (AlgebraicGeometry.AlgebraicSpace.Complexes.p f))

