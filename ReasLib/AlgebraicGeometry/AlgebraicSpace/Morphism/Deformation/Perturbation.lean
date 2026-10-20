module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Deformation.Difference
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Differentials.Pullback

/-!
# Perturbations of morphisms of first-order thickenings of algebraic spaces

A linear map from pulled-back relative differentials to the conormal sheaf
prescribes a unique perturbation with the same reduced map and conormal map.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

variable {S : Scheme.{u}}

namespace Deformation

/-- A perturbation of a morphism of first-order thickenings over `B` has the
same reduced map and conormal map, lies over `B`, and its ordered structure-map
difference is the derivation prescribed by the differential parameter. -/
def IsPerturbation {B X X' Y Y' : AlgebraicSpace S}
    (sY : Y ⟶ B) (sX' : X' ⟶ B) (sY' : Y' ⟶ B)
    (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y) (a' : X' ⟶ Y')
    [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
    (sqA : CommSq a iX iY a')
    (θ : (Modules.pullback a).obj (relativeDifferentials sY) ⟶ Hom.conormalSheaf iX)
    (b' : X' ⟶ Y') : Prop :=
  b' ≫ sY' = sX' ∧
    ∃ sqB : CommSq a iX iY b',
      Hom.Conormal.map sqA = Hom.Conormal.map sqB ∧
        structureMapDifference_restrict iX iY a a' b' sqA.w.symm sqB.w.symm =
          factorizationMap sY iX iY a
            (Hom.derivationOfPullback sY a θ)

/-- The defining conditions for a perturbation with prescribed differential map. -/
theorem isPerturbation_iff {B X X' Y Y' : AlgebraicSpace S}
    (sY : Y ⟶ B) (sX' : X' ⟶ B) (sY' : Y' ⟶ B)
    (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y) (a' : X' ⟶ Y')
    [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
    (sqA : CommSq a iX iY a')
    (θ : (Modules.pullback a).obj (relativeDifferentials sY) ⟶ Hom.conormalSheaf iX)
    (b' : X' ⟶ Y') :
    IsPerturbation sY sX' sY' iX iY a a' sqA θ b' ↔
      b' ≫ sY' = sX' ∧
        ∃ sqB : CommSq a iX iY b',
          Hom.Conormal.map sqA = Hom.Conormal.map sqB ∧
            structureMapDifference_restrict iX iY a a' b' sqA.w.symm sqB.w.symm =
              factorizationMap sY iX iY a
                (Hom.derivationOfPullback sY a θ) :=
  sorry

/-- An `𝒪_X`-linear map `θ : a^* Ω_{Y/B} ⟶ C_{X/X'}` uniquely determines a
perturbation of a morphism of first-order thickenings over `B`. -/
theorem existsUnique_perturbation {B X X' Y Y' : AlgebraicSpace S}
    (sY : Y ⟶ B) (sX' : X' ⟶ B) (sY' : Y' ⟶ B)
    (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y) (a' : X' ⟶ Y')
    [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
    (hY : iY ≫ sY' = sY) (ha : a ≫ sY = iX ≫ sX')
    (ha' : a' ≫ sY' = sX') (sqA : CommSq a iX iY a')
    (θ : (Modules.pullback a).obj (relativeDifferentials sY) ⟶ Hom.conormalSheaf iX) :
    ExistsUnique fun b' : X' ⟶ Y' ↦
      IsPerturbation sY sX' sY' iX iY a a' sqA θ b' :=
  sorry

end Deformation

end AlgebraicGeometry.AlgebraicSpace.Hom
