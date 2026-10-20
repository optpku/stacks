/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Pushforward.Affine

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

noncomputable section

universe u

/- Lemma 75.11.1. Let `S` be a scheme. Let `f : X ⟶ Y` be an affine morphism of
algebraic spaces over `S`. Then `f_*` defines a derived functor
`DerivedCategory (QCoh X) ⥤ DerivedCategory (QCoh Y)`. This functor has the
property that the canonical comparisons `DerivedCategory (QCoh _) ⥤ DerivedQCoh _`
intertwine it with restricted ambient derived pushforward. -/
@[stacks 08GY] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.pushforwardComparison_isomorphic_of_affine :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [Affine f],
      IsIsomorphic
        (QCoh.Derived.pushforward f ⋙ DerivedQCoh.comparison Y)
        (DerivedQCoh.comparison X ⋙ DerivedQCoh.pushforwardCohomologyIn f))

#check AlgebraicGeometry.AlgebraicSpace.QCoh.Derived.pushforward
#check AlgebraicGeometry.AlgebraicSpace.QCoh.Derived.pushforwardIsRightDerived
