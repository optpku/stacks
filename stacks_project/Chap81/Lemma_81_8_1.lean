/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pushout
import StacksCheckRecall

/-!
# Lemma 81.8.1

In a pushout of algebraic spaces along a thickening and an affine morphism, every
pseudo-coherent triple in the derived-module fibre product lies in the essential
image of derived pullback from `Y'`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Limits
open scoped CategoricalPullback

noncomputable section

universe u

/- Lemma 81.8.1: Let `S` be a scheme. Consider a pushout square of algebraic spaces
over `S` as in Lemma 81.6.2, and assume `i` is a thickening. Then the essential image
of the derived-pullback functor `D(𝒪_{Y'}) ⥤ D(𝒪_Y) ×_{D(𝒪_X)} D(𝒪_{X'})` contains
every triple `(M, K', α)` where `M : ModuleDerived Y` and `K' : ModuleDerived X'` are
pseudo-coherent and `α : Lf^* M ≅ Li^* K'`. -/
@[stacks 0DL7] #check
  (AlgebraicGeometry.AlgebraicSpace.modulePullbackDerived.pushoutSquareFunctor_essImage_of_pseudoCoherent :
    ∀ {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
    {i : X ⟶ X'} {f : X ⟶ Y} {f' : X' ⟶ Y'} {j : Y ⟶ Y'}
    [IsThickening i] [Affine f]
    (h : IsPushout i f f' j) (M : ModuleDerived Y) (K' : ModuleDerived X')
    (hM : IsPseudoCoherent Y M) (hK' : IsPseudoCoherent X' K')
    (α : (modulePullbackDerived f).obj M ≅ (modulePullbackDerived i).obj K'),
    (modulePullbackDerived.pushoutSquareFunctor h.toCommSq).essImage
      (CategoricalPullback.mk M K' α))

#check
  (AlgebraicGeometry.AlgebraicSpace.modulePullbackDerived.pushoutSquareFunctor_essImage_of_pseudoCoherent_obj :
    ∀ {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
    {i : X ⟶ X'} {f : X ⟶ Y} {f' : X' ⟶ Y'} {j : Y ⟶ Y'}
    [IsThickening i] [Affine f]
    (h : IsPushout i f f' j) (T : (modulePullbackDerived f) ⊡ (modulePullbackDerived i))
    (hM : IsPseudoCoherent Y T.fst) (hK' : IsPseudoCoherent X' T.snd),
    (modulePullbackDerived.pushoutSquareFunctor h.toCommSq).essImage T)

