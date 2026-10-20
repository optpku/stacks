module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.RightAdjoint

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.inclusionIsLeftAdjoint :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X],
    (inclusion X).IsLeftAdjoint)

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
