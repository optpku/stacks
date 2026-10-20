/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePresentation.Over

/-!
# Compatibility checks for algebraic spaces of finite presentation

The canonical full-subcategory API is owned by the shared finite-presentation module.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.finitePresentationOverProperty :
  (T : Scheme.{u}) → ObjectProperty (AlgebraicSpace T))

#check (AlgebraicGeometry.AlgebraicSpace.FinitePresentationOver :
  Scheme.{u} → Type (u + 1))

#check (AlgebraicGeometry.AlgebraicSpace.FinitePresentationOver.inclusion :
  (T : Scheme.{u}) → FinitePresentationOver T ⥤ AlgebraicSpace T)

#check (AlgebraicGeometry.AlgebraicSpace.FinitePresentationOver.of :
  ∀ {T : Scheme.{u}} (X : AlgebraicSpace T),
    FinitePresentation (toBase X) → FinitePresentationOver T)

#check (AlgebraicGeometry.AlgebraicSpace.FinitePresentationOver.of_obj :
  ∀ {T : Scheme.{u}} (X : AlgebraicSpace T) (h : FinitePresentation (toBase X)),
    (FinitePresentationOver.of X h).obj = X)

#check (AlgebraicGeometry.AlgebraicSpace.FinitePresentationOver.condition :
  ∀ {T : Scheme.{u}} (X : FinitePresentationOver T),
    FinitePresentation (toBase X.obj))

#check (AlgebraicGeometry.AlgebraicSpace.FinitePresentationOver.mem_iff :
  ∀ {T : Scheme.{u}} (X : AlgebraicSpace T),
    FinitePresentation (toBase X) ↔ ∃ Y : FinitePresentationOver T, Y.obj = X)

end AlgebraicGeometry.AlgebraicSpace
