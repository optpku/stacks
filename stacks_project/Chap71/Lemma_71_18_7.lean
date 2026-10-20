/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StrictTransform.Composition

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 71.18.7 (1): Strict transforms of modules agree as quotients. -/
@[stacks 0868] #check (AlgebraicGeometry.AlgebraicSpace.strictTransformModule_isomorphic_pushforward_iteratedStrictTransform :
    ∀ {S : Scheme.{u}} {B B' B'' X : AlgebraicSpace S}
    (Z : ClosedSubspace B) (b : B' ⟶ B) [IsBlowup b Z]
    (Z' : ClosedSubspace B') (b' : B'' ⟶ B') [IsBlowup b' Z']
    (Y : ClosedSubspace B)
    (hY : Y.pointsSet = Z.pointsSet ∪ Points.map b '' Z'.pointsSet)
    [IsBlowup (b' ≫ b) Y]
    (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent],
    ∃ e :
      strictTransformModule (b' ≫ b) (Y.inverseImageSubspace (b' ≫ b)) f F ≅
      (Modules.pushforward (pullbackLeftPullbackSndIso f b b').hom).obj
        (strictTransformModule b' (Z'.inverseImageSubspace b') (pullback.snd f b)
          (strictTransformModule b (Z.inverseImageSubspace b) f F)),
      strictTransformπ (b' ≫ b) (Y.inverseImageSubspace (b' ≫ b)) f F ≫ e.hom =
        iteratedStrictTransformπ b b' (Z.inverseImageSubspace b)
          (Z'.inverseImageSubspace b') f F)

/- Lemma 71.18.7 (2): Strict transforms of spaces agree over their ambient fibre product. -/
@[stacks 0868] #check (AlgebraicGeometry.AlgebraicSpace.strictTransform_isomorphic_iteratedStrictTransform :
    ∀ {S : Scheme.{u}} {B B' B'' X : AlgebraicSpace S}
    (Z : ClosedSubspace B) (b : B' ⟶ B) [IsBlowup b Z]
    (Z' : ClosedSubspace B') (b' : B'' ⟶ B') [IsBlowup b' Z']
    (Y : ClosedSubspace B)
    (hY : Y.pointsSet = Z.pointsSet ∪ Points.map b '' Z'.pointsSet)
    [IsBlowup (b' ≫ b) Y]
    (f : X ⟶ B)
    [QuasiCompact (strictTransformOpenComplement b (Z.inverseImageSubspace b) f).ι]
    [QuasiCompact
      (strictTransformOpenComplement b' (Z'.inverseImageSubspace b')
        (strictTransformSnd b (Z.inverseImageSubspace b) f)).ι]
    [QuasiCompact
      (strictTransformOpenComplement (b' ≫ b) (Y.inverseImageSubspace (b' ≫ b)) f).ι],
    ∃ e :
      (strictTransform (b' ≫ b) (Y.inverseImageSubspace (b' ≫ b)) f).X ≅
      (strictTransform b' (Z'.inverseImageSubspace b')
        (strictTransformSnd b (Z.inverseImageSubspace b) f)).X,
      e.hom ≫ iteratedStrictTransformι b b' (Z.inverseImageSubspace b)
        (Z'.inverseImageSubspace b') f =
          (strictTransform (b' ≫ b) (Y.inverseImageSubspace (b' ≫ b)) f).ι)

