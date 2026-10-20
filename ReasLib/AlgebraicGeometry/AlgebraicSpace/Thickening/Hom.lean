/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.StructureSheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening

/-!
# Morphisms of thickenings of algebraic spaces

Compatible maps of base-algebra structure sheaves determine unique morphisms
of thickenings over the base algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Thickening

variable {S : Scheme.{u}}

/-- A morphism `f' : X' ⟶ Y'` of thickenings over `B` with inverse-image structure map `α`. -/
structure IsHom {B X X' Y Y' : AlgebraicSpace S}
    (sX' : X' ⟶ B) (sY' : Y' ⟶ B)
    (iX : X ⟶ X') (iY : Y ⟶ Y') (f : X ⟶ Y)
    (α : inverseImageClosedStructureSheaf f iY ⟶ closedStructureSheaf iX)
    (f' : X' ⟶ Y') : Prop where
  /-- The pair `(f, f')` is a morphism of thickenings. -/
  w : iX ≫ f' = f ≫ iY
  /-- The morphism `f'` lies over `B`. -/
  overBase : f' ≫ sY' = sX'
  /-- The inverse-image structure map of `f'` recovers `α`. -/
  structureMap_eq : structureMap_transported iX iY f f' w = α

/-- Assemble a morphism of thickenings over `B` from the commutative square, the map over
`B`, and the identification `α = (f')^♯`. -/
def IsHom.of {B X X' Y Y' : AlgebraicSpace S}
    (sX' : X' ⟶ B) (sY' : Y' ⟶ B)
    (iX : X ⟶ X') (iY : Y ⟶ Y') (f : X ⟶ Y)
    (α : inverseImageClosedStructureSheaf f iY ⟶ closedStructureSheaf iX)
    (f' : X' ⟶ Y') (h_comm : iX ≫ f' = f ≫ iY) (h_over : f' ≫ sY' = sX')
    (hα : structureMap_transported iX iY f f' h_comm = α) :
    IsHom sX' sY' iX iY f α f' where
  w := h_comm
  overBase := h_over
  structureMap_eq := hα

/-- Being a morphism of thickenings over `B` with structure map `α` unpacks as the
commutative square, the map over `B`, and `α = (f')^♯`. -/
theorem isHom_iff {B X X' Y Y' : AlgebraicSpace S}
    (sX' : X' ⟶ B) (sY' : Y' ⟶ B)
    (iX : X ⟶ X') (iY : Y ⟶ Y') (f : X ⟶ Y)
    (α : inverseImageClosedStructureSheaf f iY ⟶ closedStructureSheaf iX)
    (f' : X' ⟶ Y') :
    IsHom sX' sY' iX iY f α f' ↔
      ∃ h_comm : iX ≫ f' = f ≫ iY,
        f' ≫ sY' = sX' ∧ structureMap_transported iX iY f f' h_comm = α :=
  sorry

/-- Let `S` be a scheme. Let `B` be an algebraic space over `S`.
Let `iX : X ⟶ X'` and `iY : Y ⟶ Y'` be thickenings of algebraic spaces over `B`,
and let `f : X ⟶ Y` be a morphism of algebraic spaces over `B`. Given any map
`α` of `sX⁻¹ 𝒪_B`-algebras `f_{spaces,étale}⁻¹ 𝒪_{Y'} ⟶ 𝒪_{X'}` on `X_spaces,étale`
making the square with `f^♯`, `iX^♯`, and `iY^♯` commute, there exists a unique
morphism `f' : X' ⟶ Y'` of thickenings over `B` such that `α = (f')^♯`. -/
@[stacks 05ZN]
theorem existsUnique_hom_of_algebraMap
    {S : Scheme.{u}} {B X X' Y Y' : AlgebraicSpace S}
    (sX : X ⟶ B) (sX' : X' ⟶ B) (sY : Y ⟶ B) (sY' : Y' ⟶ B)
    (iX : X ⟶ X') (iY : Y ⟶ Y') (f : X ⟶ Y)
    [IsThickening iX] [IsThickening iY]
    (hX : iX ≫ sX' = sX) (hY : iY ≫ sY' = sY) (hf : f ≫ sY = sX)
    (α : inverseImageClosedStructureSheaf f iY ⟶ closedStructureSheaf iX)
    (h_sq : structureMap_commutes iX iY f α)
    (h_alg : isAlgebraOverBase sX sX' sY sY' iX iY f hX hY hf α) :
    ExistsUnique fun f' : X' ⟶ Y' ↦ IsHom sX' sY' iX iY f α f' :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Thickening
