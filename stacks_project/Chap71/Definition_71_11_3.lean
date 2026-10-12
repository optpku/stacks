/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap71.Lemma_71_11_2_Functor
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.RelativeProj
open SheafOfModules.RingedSite

noncomputable section

universe u

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
variable (F : ProjFunctor X 𝒜) {deg : DegreePieces 𝒜}
variable (hF : F.IsAssociatedToQuadruples deg)

/- Definition 71.11.3

Let `S` be a scheme. Let `X` be an algebraic space over `S`. Let `𝒜` be a
quasi-coherent sheaf of graded `𝒪_X`-algebras. The relative homogeneous spectrum of
`𝒜` over `X`, or the homogeneous spectrum of `𝒜` over `X`, or the relative Proj of
`𝒜` over `X` is the algebraic space `F` over `X` of Lemma 71.11.2. We denote it
`π : underline{Proj}_X(𝒜) ⟶ X`. -/
@[stacks 084C] #check (toAlgebraicSpace_hom F hF : toAlgebraicSpace F hF ⟶ X)

#check (toAlgebraicSpace F hF : AlgebraicSpace S)

#check (toAlgebraicSpace_functorOfPoints F hF :
  (toAlgebraicSpace F hF).functorOfPoints = F.toFunctor)
