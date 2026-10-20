/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FormallyUnramified.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.UniversalFirstOrder.BaseChange
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

noncomputable section

universe u

/- Lemma 76.15.9 (1): Let `S` be a scheme. In a fibre product diagram of algebraic
spaces over `S` with `h' : W ⟶ Y` formally unramified, the base change
`h : Z ⟶ X` is formally unramified. -/
@[stacks 060B]
#check
  (AlgebraicGeometry.AlgebraicSpace.FormallyUnramified.instIsStableUnderBaseChange :
    ∀ {S : Scheme.{u}}, MorphismProperty.IsStableUnderBaseChange
      (@AlgebraicGeometry.AlgebraicSpace.FormallyUnramified S :
        MorphismProperty (AlgebraicSpace S)))

/- Lemma 76.15.9 (2): If `W ⊂ W'` is a universal first-order thickening of `W`
over `Y`, then `Z = X ×_Y W ⊂ X ×_Y W'` is a universal first-order thickening
of `Z` over `X`. -/
@[stacks 060B]
#check
  (AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder.of_isPullback :
    ∀ {S : Scheme.{u}} {X Y Z W Z' W' : AlgebraicSpace S}
    (g : X ⟶ Y) (iZ : Z ⟶ Z') (fZ : Z' ⟶ X) (iW : W ⟶ W') (fW : W' ⟶ Y)
    (f : Z ⟶ W) (f' : Z' ⟶ W') (closedSq : CommSq f iZ iW f')
    (leftSq : IsPullback f (iZ ≫ fZ) (iW ≫ fW) g)
    (rightSq : IsPullback f' fZ fW g) [IsUniversalFirstOrder iW fW],
    IsUniversalFirstOrder iZ fZ)

/- Lemma 76.15.9 (3): In particular the canonical map
`(Modules.pullback f).obj (Hom.conormalSheaf iW) ⟶ Hom.conormalSheaf iZ` of
Lemma 76.15.8 is surjective. -/
@[stacks 060B]
#check
  (AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder.conormalMap_epi :
    ∀ {S : Scheme.{u}} {X Y Z W Z' W' : AlgebraicSpace S}
    (g : X ⟶ Y) (iZ : Z ⟶ Z') (fZ : Z' ⟶ X) (iW : W ⟶ W') (fW : W' ⟶ Y)
    (f : Z ⟶ W) (f' : Z' ⟶ W')
    [IsUniversalFirstOrder iZ fZ] [IsUniversalFirstOrder iW fW]
    [FormallyUnramified (iZ ≫ fZ)] [FormallyUnramified (iW ≫ fW)]
    (leftSq : IsPullback f (iZ ≫ fZ) (iW ≫ fW) g)
    (thickeningSq : IsPullback f iZ iW f')
    (rightSq : IsPullback f' fZ fW g),
    Epi (AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder.conormalMap iZ fZ iW fW f g ⟨leftSq.w⟩))
