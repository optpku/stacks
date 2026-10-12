/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.LinearEmbedding
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

/- Exercise 111.37.2
The explicit scheme morphism `ProjectiveSpace.scheme ℂ 1 ⟶
ProjectiveSpace.scheme ℂ 5`. -/
@[stacks 029Y] #check
  (AlgebraicGeometry.ProjectiveSpace.LinearEmbedding.hom :
    AlgebraicGeometry.ProjectiveSpace.scheme ℂ 1 ⟶
      AlgebraicGeometry.ProjectiveSpace.scheme ℂ 5)

/- Exercise 111.37.2
The morphism commutes with the structure maps to `Spec ℂ`. -/
@[stacks 029Y] #check
  (AlgebraicGeometry.ProjectiveSpace.LinearEmbedding.hom_comp_toSpec :
    AlgebraicGeometry.ProjectiveSpace.LinearEmbedding.hom ≫
        AlgebraicGeometry.ProjectiveSpace.toSpec ℂ 5 =
      AlgebraicGeometry.ProjectiveSpace.toSpec ℂ 1)

/- Exercise 111.37.2
The morphism is nonconstant. -/
@[stacks 029Y] #check
  (AlgebraicGeometry.ProjectiveSpace.LinearEmbedding.isNonconstant :
    Scheme.Hom.IsNonconstant AlgebraicGeometry.ProjectiveSpace.LinearEmbedding.hom)
