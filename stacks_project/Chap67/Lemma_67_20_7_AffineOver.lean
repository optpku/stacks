module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap67.Lemma_67_20_5_Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine.Over

/-!
# Algebraic spaces affine over a base algebraic space

This file retains the historical imports and checks the shared category of
algebraic spaces with affine structure morphisms for downstream consumers.
-/

@[expose] public section

open CategoryTheory

universe u

/- The shared affine-over category remains available through this typed compatibility check. -/
#check (AlgebraicGeometry.AlgebraicSpace.AffineMorphismOver :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}, AlgebraicGeometry.AlgebraicSpace S → Type (u + 1))
