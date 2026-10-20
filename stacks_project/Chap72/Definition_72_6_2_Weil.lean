module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.Weil
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Topology.LocallyFinite
public import stacks_project.Chap72.Definition_72_6_2_Prime

universe u

#check (AlgebraicGeometry.AlgebraicSpace.WeilDivisor :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S),
    [AlgebraicGeometry.AlgebraicSpace.IsDecent X] → Type (u + 1))

#check (AlgebraicGeometry.AlgebraicSpace.instAddCommGroupWeilDivisor :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S),
    [AlgebraicGeometry.AlgebraicSpace.IsDecent X] →
    AddCommGroup (AlgebraicGeometry.AlgebraicSpace.WeilDivisor X))
