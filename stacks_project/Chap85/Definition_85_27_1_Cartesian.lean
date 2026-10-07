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
