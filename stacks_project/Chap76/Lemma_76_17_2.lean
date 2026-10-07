module

public import stacks_project.Chap76.Lemma_76_17_2_Perturbation
public import stacks_project.Chap76.Lemma_76_17_2_Comparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom.Deformation

noncomputable section

universe u

/- Lemma 76.17.2: Let `S` be a scheme. Let `B` be an algebraic space over `S`.
Let `(a, a') : (X ⊂ X') ⟶ (Y ⊂ Y')` be a morphism of first-order thickenings
over `B`. Let `θ : a^* Ω_{Y/B} ⟶ C_{X/X'}` be an `𝒪_X`-linear map. Then there
exists a unique morphism of pairs `(b, b')` such that (1) and (2) of
Lemma 76.17.1 hold and the derivation `D` of Lemma 76.17.1 satisfies
`(a')^♯ - (b')^♯ = D = d_{Y/B} ∘ θ`. -/
@[stacks 04D0] #check (existsUnique_perturbation :
    ∀ {S : Scheme.{u}} {B X X' Y Y' : AlgebraicSpace S}
      (sY : Y ⟶ B) (sX' : X' ⟶ B) (sY' : Y' ⟶ B)
      (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y) (a' : X' ⟶ Y')
      [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
      (hY : iY ≫ sY' = sY) (ha : a ≫ sY = iX ≫ sX')
      (ha' : a' ≫ sY' = sX') (sqA : CommSq a iX iY a')
      (θ : (Modules.pullback a).obj (Hom.relativeDifferentials sY) ⟶ Hom.conormalSheaf iX),
      ExistsUnique fun b' : X' ⟶ Y' ↦
        IsPerturbation sY sX' sY' iX iY a a' sqA θ b')
