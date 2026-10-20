/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import stacks_project.Chap82.Lemma_82_26_7_ProperPushforward

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

universe u

/- Lemma 82.26.7: In Situation 82.2.1 let `f : X ⟶ Y` and `g : Y ⟶ Z` be
morphisms of good algebraic spaces over `B`. Let `c ∈ A^p(X ⟶ Z)` and assume
`f` is proper. Then the rule sending a cartesian test square for `g` to
`α ↦ f'_*(c ∩ α)`, where `f'` is the base change of `f`, is a bivariant class
of degree `p` of `Y ⟶ Z`. -/
@[stacks 0ERQ] #check
  (AlgebraicGeometry.AlgebraicSpace.BivariantClass.properPushforward :
    ∀ {S : Scheme.{u}} {B X Y Z : AlgebraicSpace S}
      [UniversallyCatenary B] [IsQuasiSeparated B]
      (δ : Points B → ℤ) [IsDimensionFunction δ]
      (pZ : Z ⟶ B) [QuasiSeparated pZ] [LocallyOfFiniteType pZ]
      (f : X ⟶ Y) (g : Y ⟶ Z)
      [QuasiSeparated (g ≫ pZ)] [LocallyOfFiniteType (g ≫ pZ)]
      [QuasiSeparated ((f ≫ g) ≫ pZ)] [LocallyOfFiniteType ((f ≫ g) ≫ pZ)]
      [Proper f] (p : ℤ),
      AlgebraicGeometry.AlgebraicSpace.BivariantClass δ pZ (f ≫ g) p →
        AlgebraicGeometry.AlgebraicSpace.BivariantClass δ pZ g p)

#check
  (AlgebraicGeometry.AlgebraicSpace.BivariantClass.properPushforward_cap :
    ∀ {S : Scheme.{u}} {B X Y Z : AlgebraicSpace S}
      [UniversallyCatenary B] [IsQuasiSeparated B]
      (δ : Points B → ℤ) [IsDimensionFunction δ]
      (pZ : Z ⟶ B) [QuasiSeparated pZ] [LocallyOfFiniteType pZ]
      (f : X ⟶ Y) (g : Y ⟶ Z)
      [QuasiSeparated (g ≫ pZ)] [LocallyOfFiniteType (g ≫ pZ)]
      [QuasiSeparated ((f ≫ g) ≫ pZ)] [LocallyOfFiniteType ((f ≫ g) ≫ pZ)]
      [Proper f] (p : ℤ)
      (c : AlgebraicGeometry.AlgebraicSpace.BivariantClass δ pZ (f ≫ g) p)
      {Y' Z' : AlgebraicSpace S}
      (i : Y' ⟶ Y) (g' : Y' ⟶ Z') (h : Z' ⟶ Z)
      [QuasiSeparated (h ≫ pZ)] [LocallyOfFiniteType (h ≫ pZ)]
      [QuasiSeparated (i ≫ g ≫ pZ)] [LocallyOfFiniteType (i ≫ g ≫ pZ)]
      (square : IsPullback i g' g h) (k : ℤ),
      (AlgebraicGeometry.AlgebraicSpace.BivariantClass.properPushforward
          δ pZ f g p c).cap i g' h square k =
        (Hom.properPushforward δ (pullback.fst f i ≫ (f ≫ g) ≫ pZ)
            (i ≫ g ≫ pZ) (pullback.snd f i)
            (AlgebraicGeometry.AlgebraicSpace.BivariantClass.pullbackSnd_comp_structure
              pZ f g i) (k - p)).comp
          (c.cap (pullback.fst f i) (pullback.snd f i ≫ g') h
            (AlgebraicGeometry.AlgebraicSpace.BivariantClass.properPushforwardSquare
              f g i g' h square) k))
