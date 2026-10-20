module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.Hom
public import stacks_project.Chap76.Lemma_76_9_2_Thickening
import StacksCheckRecall

/-!
# Morphisms of thickenings of algebraic spaces from algebra maps

A compatible map of `𝒪_B`-algebras on the spaces-étale sites of thickenings
`X ⊂ X'` and `Y ⊂ Y'` is uniquely `(f')^♯` for a morphism of thickenings
`(f, f')` over `B`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Thickening

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Thickening

/- Lemma 76.9.2: Let `S` be a scheme. Let `B` be an algebraic space over `S`.
Let `iX : X ⟶ X'` and `iY : Y ⟶ Y'` be thickenings of algebraic spaces over `B`,
and let `f : X ⟶ Y` be a morphism of algebraic spaces over `B`. Given any map
`α` of `sX⁻¹ 𝒪_B`-algebras `f_{spaces,étale}⁻¹ 𝒪_{Y'} ⟶ 𝒪_{X'}` on `X_spaces,étale`
making the square with `f^♯`, `iX^♯`, and `iY^♯` commute, there exists a unique
morphism `f' : X' ⟶ Y'` of thickenings over `B` such that `α = (f')^♯`. -/
@[stacks 05ZN] #check (AlgebraicGeometry.AlgebraicSpace.Thickening.existsUnique_hom_of_algebraMap :
  ∀
    {S : Scheme.{u}} {B X X' Y Y' : AlgebraicSpace S}
    (sX : X ⟶ B) (sX' : X' ⟶ B) (sY : Y ⟶ B) (sY' : Y' ⟶ B)
    (iX : X ⟶ X') (iY : Y ⟶ Y') (f : X ⟶ Y)
    [IsThickening iX] [IsThickening iY]
    (hX : iX ≫ sX' = sX) (hY : iY ≫ sY' = sY) (hf : f ≫ sY = sX)
    (α : inverseImageClosedStructureSheaf f iY ⟶ closedStructureSheaf iX)
    (h_sq : structureMap_commutes iX iY f α)
    (h_alg : isAlgebraOverBase sX sX' sY sY' iX iY f hX hY hf α),
    ExistsUnique fun f' : X' ⟶ Y' ↦ IsHom sX' sY' iX iY f α f')

end AlgebraicGeometry.AlgebraicSpace.Thickening
