/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints

/-!
# The scheme embedding into algebraic spaces

Schemes over a fixed base are represented by algebraic spaces, and morphisms are sent to their
Yoneda transformations.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The functor sending a scheme over `S` to its represented algebraic space over `S`. -/
def schemeFunctor (S : Scheme.{u}) : Over S ⥤ AlgebraicSpace S where
  obj := ofOver
  map f := (yoneda.map f : yoneda.obj _ ⟶ yoneda.obj _)
  map_id object := yoneda.map_id object
  map_comp first second := yoneda.map_comp first second

/-- The object map of `schemeFunctor S` is `ofOver`. -/
@[simp]
theorem schemeFunctor_obj (S : Scheme.{u}) (U : Over S) :
    (schemeFunctor S).obj U = ofOver U :=
  sorry

/-- The morphism map of `schemeFunctor S` is the Yoneda image of a morphism in `Over S`. -/
@[simp]
theorem schemeFunctor_map {S : Scheme.{u}} {U V : Over S} (f : U ⟶ V) :
    (schemeFunctor S).map f = yoneda.map f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
