/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Complexes.StructureMorphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.Diagonal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.FinitePresentation

/-! # Affineness and finite presentation of the relative complexes-stack diagonal -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.CohStack.Hom renaming Affine → RepresentablyAffine,
  FinitePresentation → RepresentablyOfFinitePresentation, diagonal → relativeDiagonal
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Complexes

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- For a proper, flat morphism of finite presentation, the relative diagonal
over the base of the stack of admissible relatively perfect complexes is affine. -/
instance instAffine_diagonal (f : X ⟶ B)
    [Proper f] [Flat f] [AlgebraicSpace.FinitePresentation f] :
    RepresentablyAffine (relativeDiagonal (toBase f)) := sorry

/-- For a proper, flat morphism of finite presentation, the relative diagonal
over the base of the stack of admissible relatively perfect complexes is of finite presentation. -/
instance instFinitePresentation_diagonal (f : X ⟶ B)
    [Proper f] [Flat f] [AlgebraicSpace.FinitePresentation f] :
    RepresentablyOfFinitePresentation (relativeDiagonal (toBase f)) := sorry

end AlgebraicGeometry.AlgebraicSpace.Complexes
