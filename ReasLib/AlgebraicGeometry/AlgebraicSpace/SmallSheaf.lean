/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints

/-!
# Small fppf sheaves of points

This module packages the functor of points of an algebraic space as a sheaf valued in
the small universe used by the underlying site.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The functor of points of an algebraic space, as an object of the small-valued fppf sheaf
category on schemes over the base. -/
def toSmallSheaf {S : Scheme.{u}} (F : AlgebraicSpace S) :
    Sheaf (Scheme.fppfTopology.over S) (Type u) :=
  ⟨F.functorOfPoints, F.isSheaf⟩

/-- The underlying presheaf of the small-valued fppf sheaf of an algebraic space is its
functor of points. -/
theorem toSmallSheaf_obj {S : Scheme.{u}} (F : AlgebraicSpace S) :
    (toSmallSheaf F).obj = F.functorOfPoints := rfl

/-- A morphism of algebraic spaces induces a morphism of their small-valued fppf sheaves
of points. -/
def toSmallSheafMap {S : Scheme.{u}} {F G : AlgebraicSpace S} (φ : F ⟶ G) :
    toSmallSheaf F ⟶ toSmallSheaf G :=
  ObjectProperty.homMk φ

/-- The underlying presheaf morphism of the small-sheaf map induced by a morphism of
algebraic spaces is the original morphism. -/
theorem toSmallSheafMap_hom {S : Scheme.{u}} {F G : AlgebraicSpace S} (φ : F ⟶ G) :
    (toSmallSheafMap φ).hom = φ :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
