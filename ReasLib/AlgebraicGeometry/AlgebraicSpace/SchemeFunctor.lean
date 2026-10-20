/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The functor sending a scheme over `S` to the associated algebraic space over `S`. -/
def ofOverFunctor (S : Scheme.{u}) : Over S ⥤ AlgebraicSpace S where
  obj := ofOver
  map f := (yoneda.map f : yoneda.obj _ ⟶ yoneda.obj _)
  map_id := yoneda.map_id
  map_comp := yoneda.map_comp

/-- The object map of `ofOverFunctor S` is `ofOver`. -/
@[simp]
theorem ofOverFunctor_obj (S : Scheme.{u}) (U : Over S) :
    (ofOverFunctor S).obj U = ofOver U := sorry

/-- The morphism map of `ofOverFunctor S` is the Yoneda image of a morphism in `Over S`. -/
@[simp]
theorem ofOverFunctor_map {S : Scheme.{u}} {U V : Over S} (f : U ⟶ V) :
    (ofOverFunctor S).map f = yoneda.map f := sorry

variable {S : Scheme.{u}}

/-- The morphism in `Over S` recovered from a morphism of algebraic spaces between schemes
over `S`. -/
def ofOverPreimage {U V : Over S} (φ : ofOver U ⟶ ofOver V) : U ⟶ V :=
  Yoneda.fullyFaithful.preimage (φ : yoneda.obj U ⟶ yoneda.obj V)

/-- `ofOverMap` inverts `ofOverPreimage`. -/
theorem ofOverMap_preimage {U V : Over S} (φ : ofOver U ⟶ ofOver V) :
    ofOverMap (ofOverPreimage φ) = φ :=
  sorry

/-- `ofOverPreimage` inverts `ofOverMap`. -/
theorem ofOverPreimage_map {U V : Over S} (g : U ⟶ V) :
    ofOverPreimage (ofOverMap g) = g :=
  sorry


end AlgebraicGeometry.AlgebraicSpace
