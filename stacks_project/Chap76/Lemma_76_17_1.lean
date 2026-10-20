module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Deformation.DifferenceConstruction
public import stacks_project.Chap76.Lemma_76_17_1_Difference
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom.Deformation

noncomputable section

universe u

/- Lemma 76.17.1: Let `S` be a scheme. Let `B` be an algebraic space over `S`.
Let `X ⊂ X'` and `Y ⊂ Y'` be two first-order thickenings of algebraic spaces
over `B`. Let `(a, a'), (b, b') : (X ⊂ X') ⟶ (Y ⊂ Y')` be two morphisms of
thickenings over `B`. Assume that `a = b`, and the two maps
`a^* C_{Y/Y'} ⟶ C_{X/X'}` (Lemma 76.5.3) are equal. Then the map
`(a')^♯ - (b')^♯` factors as `𝒪_{Y'} ⟶ 𝒪_Y ⟶^D a_* C_{X/X'} ⟶ a_* 𝒪_{X'}`
where `D` is an `𝒪_B`-derivation. -/
@[stacks 0618] #check (AlgebraicGeometry.AlgebraicSpace.Hom.Deformation.exists_differenceDerivation :
  ∀ {S : Scheme.{u}} {B X X' Y Y' : AlgebraicSpace S}
    (sY : Y ⟶ B) (sX' : X' ⟶ B) (sY' : Y' ⟶ B)
    (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y) (a' b' : X' ⟶ Y')
    [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
    (hY : iY ≫ sY' = sY) (ha : a ≫ sY = iX ≫ sX')
    (ha' : a' ≫ sY' = sX') (hb' : b' ≫ sY' = sX')
    (sqA : CommSq a iX iY a') (sqB : CommSq a iX iY b')
    (hconormal : Hom.Conormal.map sqA = Hom.Conormal.map sqB),
    ∃ D : Hom.derivations sY ((Modules.pushforward a).obj (Hom.conormalSheaf iX)),
      structureMapDifference_restrict iX iY a a' b' sqA.w.symm sqB.w.symm =
        factorizationMap sY iX iY a D)
