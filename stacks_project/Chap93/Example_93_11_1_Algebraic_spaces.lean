/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.AlgebraicSpace.Category
public import ReasLib.AlgebraicGeometry.FormalDeformation.AlgebraicSpace.Deformation
import StacksCheckRecall

/-!
# Algebraic spaces

Source-facing labeled entries for the category `F` of pairs `(A, X)` of an
object of `ArtinianLocalAlgCat` with an algebraic space flat over `A`, the
cofibered projection `p`, and the deformation category `Def_X = F_{x0}`.
-/

@[expose] public section

open CategoryTheory Functor FlatAlgebraicSpaceCat

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/- Example 93.11.1 (Algebraic spaces) (1)
Let F be the category FlatAlgebraicSpaceCat of pairs (A, X) consisting of an
object A of ArtinianLocalAlgCat Λ k and an algebraic space X flat over A. A
morphism (f, g) : (B, Y) ⟶ (A, X) consists of a morphism f : B ⟶ A in
ArtinianLocalAlgCat Λ k together with a morphism g : X ⟶ Y of algebraic spaces
over Λ such that the square X ⟶ Y over Spec(A) ⟶ Spec(B) is cartesian. -/
@[stacks 0E3Z]
#check (FlatAlgebraicSpaceCat Λ k : Type (u + 1))

/- Example 93.11.1 (Algebraic spaces) (2)
The functor p = FlatAlgebraicSpaceCat.forget sends (A, X) to A and (f, g) to f,
and is cofibered in groupoids. -/
@[stacks 0E3Z]
#check (FlatAlgebraicSpaceCat.instIsFiberedInGroupoids_forget Λ k :
  IsFibered.InGroupoids (FlatAlgebraicSpaceCat.forget Λ k).op)

variable (X : AlgebraicGeometry.AlgebraicSpace (AlgebraicGeometry.Spec (CommRingCat.of k)))

/- Example 93.11.1 (Algebraic spaces) (3)
Given an algebraic space X over k, let x0 = (k, X) be ofResidue X in the fibre
F(k). The deformation category is Def_X = deformation X = F_{x0}. -/
@[stacks 0E3Z]
#check (FlatAlgebraicSpaceCat.deformation Λ k X : Type (u + 1))
