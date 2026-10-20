module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.UniversalFirstOrder.FlatBaseChange
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

noncomputable section

universe u

/- Lemma 76.15.10 (1): Let `S` be a scheme. In a fibre product diagram of algebraic
spaces over `S` with `h' : W ⟶ Y` formally unramified and `g : X ⟶ Y` flat, the
corresponding map `Z' ⟶ W'` of universal first-order thickenings is flat. -/
@[stacks 060C]
#check
  (AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder.comparison_flat :
    ∀ {S : Scheme.{u}} {X Y Z W Z' W' : AlgebraicSpace S}
      (g : X ⟶ Y) (iZ : Z ⟶ Z') (fZ : Z' ⟶ X) (iW : W ⟶ W') (fW : W' ⟶ Y)
      (f : Z ⟶ W) [IsUniversalFirstOrder iZ fZ] [IsUniversalFirstOrder iW fW]
      [FormallyUnramified (iZ ≫ fZ)] [FormallyUnramified (iW ≫ fW)] [Flat g]
      (leftSq : IsPullback f (iZ ≫ fZ) (iW ≫ fW) g),
      Flat (IsUniversalFirstOrder.comparison iZ fZ iW fW f g ⟨leftSq.w⟩))

/- Lemma 76.15.10 (2): In this case the canonical map
`(Modules.pullback f).obj (Hom.conormalSheaf iW) ⟶ Hom.conormalSheaf iZ` is an
isomorphism. -/
@[stacks 060C]
#check
  (AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder.conormalMap_isIso :
    ∀ {S : Scheme.{u}} {X Y Z W Z' W' : AlgebraicSpace S}
      (g : X ⟶ Y) (iZ : Z ⟶ Z') (fZ : Z' ⟶ X) (iW : W ⟶ W') (fW : W' ⟶ Y)
      (f : Z ⟶ W) [IsUniversalFirstOrder iZ fZ] [IsUniversalFirstOrder iW fW]
      [FormallyUnramified (iZ ≫ fZ)] [FormallyUnramified (iW ≫ fW)] [Flat g]
      (leftSq : IsPullback f (iZ ≫ fZ) (iW ≫ fW) g),
      IsIso (IsUniversalFirstOrder.conormalMap iZ fZ iW fW f g ⟨leftSq.w⟩))
