/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Picard.WithSection
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoids
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.Sites.Over

/-!
# The Picard stack rigidified along a section

The rigidified Picard projection is a stack in groupoids for the fppf topology,
and its fibers are essentially small.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Picard.WithSection

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The Picard projection rigidified along a section is a stack in groupoids
for the fppf topology on schemes over `S`. -/
instance isStackInGroupoids (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B) :
    IsStack.InGroupoids (Scheme.fppfTopology.over S) (p f σ hσ) := sorry

/-- Every fiber of the Picard projection rigidified along a section is
essentially `u`-small. -/
instance fibers_essentiallySmall (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B)
    (U : Over S) :
    ObjectProperty.EssentiallySmall.{u}
      (⊤ : ObjectProperty ((p f σ hσ).Fiber U)) := sorry

end AlgebraicGeometry.AlgebraicSpace.Picard.WithSection
