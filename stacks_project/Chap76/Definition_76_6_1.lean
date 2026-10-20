module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.Algebra
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

variable {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i]

/- Definition 76.6.1: Let `i : Z ⟶ X` be an immersion of algebraic spaces. The
conormal algebra `C_{Z/X,*}` of `Z` in `X`, or the conormal algebra of `i`, is
the quasi-coherent sheaf of graded `𝒪_Z`-algebras `⊕_{n ≥ 0} ℐ^n / ℐ^{n+1}`
of the coborder closed immersion `liftCoborder i : Z ⟶ X \ ∂Z`. -/
@[stacks 09RN]
#check (AlgebraicGeometry.AlgebraicSpace.ConormalAlgebra.total i : Z.QcAlgebraUnder)
