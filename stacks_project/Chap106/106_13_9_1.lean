module

import StacksCheckRecall
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

variable {S : Scheme.{u}} {Xi X : GroupoidsOver S} [AlgebraicStack Xi] [AlgebraicStack X]
variable {Mi M : AlgebraicSpace S}
variable (gi : Xi ⟶ X) (fi : Xi ⟶ Mi.toGroupoids) (f : X ⟶ M.toGroupoids) (φ : Mi ⟶ M)
variable (γ : gi ≫ f ≅ fi ≫ AlgebraicSpace.toGroupoids.map φ)

/- 106.13.9.1: after forming the algebraic space `M = U / R`, there is a
canonical 1-morphism `f : X ⟶ M.toGroupoids` fitting into the 2-commutative
square with top `g_i : X_i ⟶ X`, left vertical `f_i : X_i ⟶ M_i.toGroupoids`,
right vertical `f`, and bottom `AlgebraicSpace.toGroupoids.map φ` for
`φ : M_i ⟶ M`. The 2-cell is `γ : g_i ≫ f ≅ f_i ≫ AlgebraicSpace.toGroupoids.map φ`.
Cartesianness of this square is a later claim, not this displayed equation. -/
@[stacks 0DUU] #check (⟨Xi, gi, fi, γ⟩ : Bicategory.PseudoPullbackCone f (AlgebraicSpace.toGroupoids.map φ))
