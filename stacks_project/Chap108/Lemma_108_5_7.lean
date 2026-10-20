/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.ClosedImmersion

/-!
# Lemma 108.5.7

A closed immersion of separated finite-presentation algebraic spaces over `B`
induces an isomorphism of Grothendieck Quot functors by fibrewise pushforward.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Opposite

universe u

/- Lemma 108.5.7: if `π : X ⟶ Y` is a closed immersion of algebraic spaces
which are separated and of finite presentation over an algebraic space `B`,
and `F` is a quasi-coherent `𝒪_X`-module, then the morphism
`Quot.map π y F : Quot.quot (π ≫ y) F ⟶ Quot.quot y ((Modules.pushforward π).obj F)` of
Lemma 108.5.4 is an isomorphism. -/
@[stacks 0DP4] #check (AlgebraicGeometry.AlgebraicSpace.Quot.isIso_map :
  ∀ {S : Scheme.{u}} {X Y B : AlgebraicSpace S} (π : X ⟶ Y) (y : Y ⟶ B)
    [IsClosedImmersion π]
    [Separated (π ≫ y)] [FinitePresentation (π ≫ y)]
    [Separated y] [FinitePresentation y]
    (F : X.Modules) [F.IsQuasicoherent],
    IsIso (AlgebraicSpace.Quot.map π y F))

/- The morphism of Lemma 108.5.4 is bijective on `T`-points for every scheme
`T` over `B`. -/
#check (AlgebraicGeometry.AlgebraicSpace.Quot.map_app_bijective :
  ∀ {S : Scheme.{u}} {X Y B : AlgebraicSpace S} (π : X ⟶ Y) (y : Y ⟶ B)
    [IsClosedImmersion π]
    [Separated (π ≫ y)] [FinitePresentation (π ≫ y)]
    [Separated y] [FinitePresentation y]
    (F : X.Modules) [F.IsQuasicoherent]
    (σ : (SchemeOver B)ᵒᵖ),
    Function.Bijective ((AlgebraicSpace.Quot.map π y F).app σ))
