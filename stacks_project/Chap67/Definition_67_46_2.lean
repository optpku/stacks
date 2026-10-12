/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_46_2_FiniteLocallyFree
import StacksCheckRecall

@[expose] public section

/- Definition 67.46.2 (1): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`
is finite locally free if it is affine and `f_* 𝒪_X` is a finite locally free `𝒪_Y`-module. -/
@[stacks 03ZV] #check AlgebraicGeometry.AlgebraicSpace.FiniteLocallyFree

/- Definition 67.46.2 (2): a finite locally free morphism `f : X ⟶ Y` of algebraic spaces
over a scheme `S` has rank or degree `d` if `f_* 𝒪_X` is finite locally free of rank `d`. -/
@[stacks 03ZV] #check AlgebraicGeometry.AlgebraicSpace.FiniteLocallyFreeOfRank
