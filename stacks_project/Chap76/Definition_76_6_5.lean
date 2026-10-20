module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.NormalCone
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

variable {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i]

/- Definition 76.6.5 (1): The normal cone of an immersion `i : Z ⟶ X` of algebraic
spaces over `S` is the relative spectrum over `Z` of the total conormal algebra. -/
@[stacks 09RU]
#check (AlgebraicGeometry.AlgebraicSpace.normalCone_eq_relativeSpec i :
  AlgebraicGeometry.AlgebraicSpace.normalCone i =
    AlgebraicGeometry.AlgebraicSpace.relativeSpec
      (AlgebraicGeometry.AlgebraicSpace.ConormalAlgebra.total i))

/- Definition 76.6.5 (2): The normal bundle of an immersion `i : Z ⟶ X` of algebraic
spaces over `S` is the relative spectrum over `Z` of the symmetric algebra of its
conormal sheaf. -/
@[stacks 09RU]
#check (AlgebraicGeometry.AlgebraicSpace.normalBundle_eq_relativeSpec i :
  AlgebraicGeometry.AlgebraicSpace.normalBundle i =
    AlgebraicGeometry.AlgebraicSpace.relativeSpec
      (AlgebraicGeometry.AlgebraicSpace.ConormalAlgebra.symmetric i))
