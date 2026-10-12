/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Cartesian
public import Mathlib.AlgebraicGeometry.Scheme
import StacksCheckRecall

universe u

/- Definition 85.27.1: a morphism `a : Y ⟶ X` of simplicial schemes is cartesian, or that
`Y` is cartesian over `X`, iff `CategoryTheory.SimplicialObject.IsCartesian a`.
This is equivalent to `CategoryTheory.NatTrans.Equifibered a`: for `φ : n ⟶ m` in
`SimplexCategory`, the defining square
`IsPullback (a.app (op m)) (Y.map φ.op) (X.map φ.op) (a.app (op n))`
is `IsPullback.flip` of Equifibered's square on `φ.op`. -/
@[stacks 0249] #check (@CategoryTheory.SimplicialObject.IsCartesian _ _ :
  CategoryTheory.MorphismProperty (CategoryTheory.SimplicialObject AlgebraicGeometry.Scheme.{u}))
