/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.CatCommSqOver

/-!
# Derived pullback squares of algebraic spaces

A commutative square of algebraic spaces induces a comparison functor from the
derived module category of its terminal vertex to the categorical pullback of
the derived module categories of its other vertices.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
open CategoricalPullback
open scoped CategoricalPullback

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
variable {i : X ⟶ X'} {f : X ⟶ Y} {f' : X' ⟶ Y'} {j : Y ⟶ Y'}

/-- A commutative square of algebraic spaces canonically gives a commutative
square of derived module pullbacks. -/
def modulePullbackDerived.pushoutSquare (sq : CommSq i f f' j) :
    CatCommSqOver (modulePullbackDerived f) (modulePullbackDerived i)
      (ModuleDerived Y') where
  fst := modulePullbackDerived j
  snd := modulePullbackDerived f'
  iso := Hom.DerivedBaseChange.pullbackCartesianIso sq

/-- Derived pullback along the two legs of a commutative square defines a
functor to the categorical pullback of the derived module categories. -/
def modulePullbackDerived.pushoutSquareFunctor (sq : CommSq i f f' j) :
    ModuleDerived Y' ⥤ (modulePullbackDerived f) ⊡ (modulePullbackDerived i) :=
  (modulePullbackDerived.pushoutSquare sq).comparison

end AlgebraicGeometry.AlgebraicSpace
