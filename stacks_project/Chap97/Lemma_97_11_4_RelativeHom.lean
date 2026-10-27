/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.CategoryTheory.Yoneda
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap65.Lemma_65_7_2_Pullback
public import stacks_project.Chap66.Definition_66_4_1_Points

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeHom
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf

/-!
# Universe-raised sheaves of points and relative morphisms

Transparent compatibility names for the canonical sheaf of points and relative morphisms.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Universe-raised functor of points of an algebraic space over `S`. -/
abbrev uliftFunctorOfPoints {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (Over S)ᵒᵖ ⥤ Type (u + 1) :=
  (AlgebraicSpace.toSheaf.obj X).obj

/-- The fppf sheaf on `Over S` obtained by universe-raising the functor of points. -/
abbrev uliftSheafOfPoints {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  AlgebraicSpace.toSheaf.obj X

namespace RelativeHom

/-- A point of the relative-morphism presheaf over a test scheme. -/
abbrev Point {S : Scheme.{u}} {Z X B : AlgebraicSpace S}
    (g : Z ⟶ B) (h : X ⟶ B) (T : Over S) : Type (u + 1) :=
  Pair g h T

/-- A map from the base change to `X` satisfying the triangle over `B`
determines a relative-morphism point. -/
def Point.of {S : Scheme.{u}} {Z X B : AlgebraicSpace S}
    {g : Z ⟶ B} {h : X ⟶ B} {T : Over S}
    (a : ofOver T ⟶ B) (b : Limits.pullback a g ⟶ X)
    (w : b ≫ h = Limits.pullback.fst a g ≫ a) : Point g h T :=
  mk a (BaseChangeMorphism.ofMap b w)

end RelativeHom

end AlgebraicGeometry.AlgebraicSpace
