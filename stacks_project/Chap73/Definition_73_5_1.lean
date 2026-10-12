/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap73.Definition_73_5_1_Covering
import StacksCheckRecall

@[expose] public section

/- Definition 73.5.1: a smooth covering of an algebraic space `X` over a scheme `S`
is a family of morphisms `{f_i : X_i ⟶ X}_{i ∈ I}` of algebraic spaces over `S`
such that each `f_i` is smooth and `|X| = ⋃_i |f_i|(|X_i|)`, i.e. the morphisms
are jointly surjective. -/
@[stacks 041C] #check AlgebraicGeometry.AlgebraicSpace.SmoothCovering

#check AlgebraicGeometry.AlgebraicSpace.smoothCovering_iff

#check AlgebraicGeometry.AlgebraicSpace.SmoothCovering.covers_union
