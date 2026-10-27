/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.StructureMorphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.Diagonal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.FinitePresentation

/-!
# Affineness and finite presentation of the coherent-sheaf diagonal
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace (Separated)
open AlgebraicGeometry.AlgebraicSpace.CohStack (forget)
open AlgebraicGeometry.AlgebraicSpace.CohStack.Hom renaming Affine → RepresentablyAffine,
  FinitePresentation → RepresentablyOfFinitePresentation, diagonal → relativeDiagonal
open scoped Bicategory

noncomputable section

universe u

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- For a separated morphism `f : X ⟶ B` of finite presentation, the relative
diagonal `relativeDiagonal (forget f)` of the stack of coherent sheaves over `B`
is affine. -/
instance AlgebraicGeometry.AlgebraicSpace.CohStack.instAffine_diagonal (f : X ⟶ B)
    [AlgebraicGeometry.AlgebraicSpace.FinitePresentation f] [Separated f] :
    RepresentablyAffine (relativeDiagonal (forget f)) := sorry

/-- For a separated morphism `f : X ⟶ B` of finite presentation, the relative
diagonal `relativeDiagonal (forget f)` of the stack of coherent sheaves over `B`
is of finite presentation. -/
instance AlgebraicGeometry.AlgebraicSpace.CohStack.instFinitePresentation_diagonal (f : X ⟶ B)
    [AlgebraicGeometry.AlgebraicSpace.FinitePresentation f] [Separated f] :
    RepresentablyOfFinitePresentation (relativeDiagonal (forget f)) := sorry
