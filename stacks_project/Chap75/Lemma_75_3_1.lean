/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap75.Lemma_75_3_1_Comparison
public import stacks_project.Chap75.Lemma_75_3_1_Pushforward
public import stacks_project.Chap75.Lemma_75_3_1_Restrict
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.Limits

noncomputable section

universe u

/- Lemma 75.3.1: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S`. Given an étale morphism `V ⟶ Y`, set `U = V ×_Y X` and denote
`g : U ⟶ V` the projection morphism. Then `(Rf_* E)|_V ≅ Rg_*(E|_U)` for `E` in
`D(𝒪_X)`. -/
@[stacks 08GE] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.derivedPushforwardEtaleBaseChangeIso_of_hasPullback :
    ∀ {S : Scheme.{u}} {X Y V : AlgebraicSpace S} (f : X ⟶ Y) (g : V ⟶ Y)
      [Etale g] [HasPullback f g] (E : ModuleDerived X),
      (restrictFunctorDerived g).obj ((moduleDerivedPushforward f).obj E) ≅
        (moduleDerivedPushforward (Limits.pullback.snd f g)).obj
          ((restrictFunctorDerived (Limits.pullback.fst f g)).obj E))
