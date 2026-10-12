/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.Definition_76_6_5_Conormal
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
#check (ConormalAlgebra.total i : Z.QcAlgebraUnder)
