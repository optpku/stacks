module

import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
import ReasLib.CategoryTheory.Monoidal.Mod
import stacks_project.Chap78.Definition_78_5_1_Group
import StacksCheckRecall

universe u

open AlgebraicGeometry CategoryTheory MonoidalCategory MonObj

variable (S : Scheme.{u}) (B : AlgebraicSpace S) (G : GroupAlgebraicSpace B)
  (X : Over B) (A : ModObj G.X X)

/- 78.8.1.1: An action `a : G ×_B X ⟶ X` of the group algebraic space `G` on
the algebraic space `X` over `B` is equivalently the pair of commutative
diagrams given by `CategoryTheory.ModObj.laws`: associativity
`(μ[G.X] ▷ X) ≫ A.smul = (α_ G.X G.X X).hom ≫ (G.X ◁ A.smul) ≫ A.smul`
(with `a = A.smul`, `1_G × a = G.X ◁ A.smul` via `α_`, and `m × 1_X = μ[G.X] ▷ X`)
and unitality `(η[G.X] ▷ X) ≫ A.smul = (λ_ X).hom`
(with `e × 1_X = η[G.X] ▷ X` and `1_X = (λ_ X).hom`). -/
@[stacks 043R] #check
  (CategoryTheory.ModObj.laws G.X X A :
    (μ[G.X] ▷ X) ≫ A.smul = (α_ G.X G.X X).hom ≫ (G.X ◁ A.smul) ≫ A.smul ∧
      (η[G.X] ▷ X) ≫ A.smul = (λ_ X).hom)
