/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.HStack
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u v

/- Lemma 59.104.8: small étale sheaves and their isomorphisms form a stack in groupoids
over the big h site of every represented base scheme. -/
@[stacks 0GF5] #check (AlgebraicGeometry.Scheme.EtaleSheaf.overCoreForget_isStack :
  (Schh : ChosenBigHSite.{u, v}) → (S : Schh.carrier) →
    CategoryTheory.IsStack.InGroupoids (ChosenBigHSite.bigTopology Schh S)
      (CategoryTheory.Pseudofunctor.CoGrothendieck.forget
        (AlgebraicGeometry.Scheme.EtaleSheaf.overCorePseudofunctor Schh S)))

#check (AlgebraicGeometry.Scheme.EtaleSheaf.overPseudofunctor_isStack :
  (Schh : ChosenBigHSite.{u, v}) → (S : Schh.carrier) →
    CategoryTheory.Pseudofunctor.IsStack
      (AlgebraicGeometry.Scheme.EtaleSheaf.overPseudofunctor Schh S)
      (ChosenBigHSite.bigTopology Schh S))
