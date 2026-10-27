/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.BaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.RelativeProj
open SheafOfModules.RingedSite

noncomputable section

universe u

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}

/- Definition 71.11.3

Let `S` be a scheme. Let `X` be an algebraic space over `S`. Let `𝒜` be a
quasi-coherent sheaf of graded `𝒪_X`-algebras. The relative homogeneous spectrum of
`𝒜` over `X`, or the homogeneous spectrum of `𝒜` over `X`, or the relative Proj of
`𝒜` over `X` is the algebraic space `F` over `X` of Lemma 71.11.2. We denote it
`π : underline{Proj}_X(𝒜) ⟶ X`. -/
@[stacks 084C] #check (AlgebraicGeometry.AlgebraicSpace.RelativeProj.toAlgebraicSpace_hom :
  ∀ (F : ProjFunctor X 𝒜) {deg : DegreePieces 𝒜} (hF : F.IsAssociatedToQuadruples deg),
    toAlgebraicSpace F hF ⟶ X)

#check (AlgebraicGeometry.AlgebraicSpace.RelativeProj.toAlgebraicSpace :
  ∀ (F : ProjFunctor X 𝒜) {deg : DegreePieces 𝒜} (hF : F.IsAssociatedToQuadruples deg),
    AlgebraicSpace S)

#check (AlgebraicGeometry.AlgebraicSpace.RelativeProj.toAlgebraicSpace_functorOfPoints :
  ∀ (F : ProjFunctor X 𝒜) {deg : DegreePieces 𝒜} (hF : F.IsAssociatedToQuadruples deg),
    (toAlgebraicSpace F hF).functorOfPoints = F.toFunctor)
