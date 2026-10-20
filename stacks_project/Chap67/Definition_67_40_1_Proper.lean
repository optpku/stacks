module

public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_9_2_Closed
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper

open CategoryTheory

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Proper :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S},
    (X ⟶ Y) → Prop)
