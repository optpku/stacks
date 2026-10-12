/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Cartesian

/-!
# Cartesian morphisms of simplicial objects: compatibility bridge

A morphism of simplicial objects is cartesian when every simplex-operator
naturality square is a pullback.
-/

universe v u

variable (C : Type u) [CategoryTheory.Category.{v} C]

#check (@CategoryTheory.SimplicialObject.IsCartesian _ _ :
  CategoryTheory.MorphismProperty (CategoryTheory.SimplicialObject C))
