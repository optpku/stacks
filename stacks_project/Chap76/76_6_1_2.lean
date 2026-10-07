module

public import stacks_project.Chap76.«76_6_1_2_Comparison»
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

variable {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i]

/- 76.6.1.2: For an immersion `i : Z ⟶ X` of algebraic spaces there is a canonical
surjective morphism of quasi-coherent graded `𝒪_Z`-algebras
`Sym^*(Hom.conormalSheaf i) ⟶ ConormalAlgebra.total i` which is an isomorphism in
degrees `0` and `1`. -/
@[stacks 09RQ] #check
  (ConormalAlgebra.symmetricToTotal i :
    SymmetricAlgebra.qcAlgebra (Hom.conormalSheaf i) ⟶ ConormalAlgebra.total i)
