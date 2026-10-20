module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteTypePoints
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap67.Definition_67_40_1_FiniteType

/-!
# Finite type points of an algebraic space

A point of an algebraic space `X` over a scheme `S` is of finite type when it
is represented by a morphism `Spec(k) ⟶ X` that is locally of finite type,
Stacks Lemma 67.25.1 (1) and Definition 67.25.3.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

#check (AlgebraicGeometry.AlgebraicSpace.IsFiniteTypePoint :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S},
    AlgebraicGeometry.AlgebraicSpace.Points X → Prop)
