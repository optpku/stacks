module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.HenselianLocalRing.Defs
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.RingTheory.Henselian
public import ReasLib.Algebra.Category.CommRingCat.ULift
public import stacks_project.Chap68.Definition_68_11_5_Neighborhood
public import stacks_project.Chap68.Lemma_68_12_8_Decent

/-!
# Henselian local rings of decent algebraic spaces

The canonical definitions and their API are owned by `ReasLib.AlgebraicGeometry.AlgebraicSpace.HenselianLocalRing.Defs`.
This chapter module preserves the original import surface.
-/

universe u

#check (AlgebraicGeometry.AlgebraicSpace.henselianLocalRing :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S)
    [AlgebraicGeometry.AlgebraicSpace.IsDecent X]
    (x : AlgebraicGeometry.AlgebraicSpace.Points X), Type (u + 1))
