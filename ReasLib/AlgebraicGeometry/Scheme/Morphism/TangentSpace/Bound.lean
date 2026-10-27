/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.TangentSpace.Basic
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A scheme morphism has embedding dimension at most `e` if every relative tangent space
has residue-field rank at most the finite cardinal `e`. -/
def HasEmbeddingDimensionLE {X Y : Scheme.{u}} (f : X ⟶ Y) (e : ℕ) : Prop :=
  ∀ x : X, Module.rank (X.residueField x) (relativeTangentSpaceAt f x) ≤ (e : Cardinal)

/-- An embedding-dimension bound is equivalent to the corresponding cardinal-rank bound
at every source point. -/
theorem hasEmbeddingDimensionLE_iff {X Y : Scheme.{u}} (f : X ⟶ Y) (e : ℕ) :
    f.HasEmbeddingDimensionLE e ↔
      ∀ x : X, Module.rank (X.residueField x) (relativeTangentSpaceAt f x) ≤ (e : Cardinal) := sorry

/-- A smooth morphism of relative dimension `e` has embedding dimension at most `e`. -/
theorem hasEmbeddingDimensionLE_of_smoothOfRelativeDimension
    {X Y : Scheme.{u}} (f : X ⟶ Y) (e : ℕ) [SmoothOfRelativeDimension e f] :
    f.HasEmbeddingDimensionLE e := sorry

end AlgebraicGeometry.Scheme.Hom
