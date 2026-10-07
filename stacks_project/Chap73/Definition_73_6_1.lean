module

public import stacks_project.Chap73.Definition_73_6_1_Covering
import StacksCheckRecall

@[expose] public section

/- Definition 73.6.1: a syntomic covering of an algebraic space `X` over a scheme `S`
is a family of morphisms `{f_i : X_i ⟶ X}_{i ∈ I}` of algebraic spaces over `S`
such that each `f_i` is syntomic and `|X| = ⋃_i |f_i|(|X_i|)`, i.e. the morphisms
are jointly surjective. -/
@[stacks 041A] #check AlgebraicGeometry.AlgebraicSpace.SyntomicCovering

#check AlgebraicGeometry.AlgebraicSpace.syntomicCovering_iff

#check AlgebraicGeometry.AlgebraicSpace.SyntomicCovering.covers_union
