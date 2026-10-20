/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeDimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FiberDimension.Locus
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.InverseImage

/-! # Largest source opens of bounded relative dimension -/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A locally finite-type morphism of algebraic spaces has a largest open source
subspace on which its relative dimension is at most a given natural number. -/
theorem exists_isLargestSourceOpen_relativeDimensionLE {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f] (d : ℕ) :
    ∃ W : OpenSubspace X, (RelativeDimensionLE (W.ι ≫ f) d ∧
      ∀ U : OpenSubspace X, RelativeDimensionLE (U.ι ≫ f) d →
        U.pointsSet ⊆ W.pointsSet) :=
  sorry

/-- The largest open source subspace on which `f` has relative dimension at most
`d` is stable under arbitrary base change. -/
theorem isLargestSourceOpen_relativeDimensionLE_pullback {S : Scheme.{u}}
    {X Y Y' : AlgebraicSpace S} (f : X ⟶ Y) (g : Y' ⟶ Y)
    [LocallyOfFiniteType f] (d : ℕ) (W : OpenSubspace X)
    (hW : (RelativeDimensionLE (W.ι ≫ f) d ∧
      ∀ U : OpenSubspace X, RelativeDimensionLE (U.ι ≫ f) d →
        U.pointsSet ⊆ W.pointsSet)) :
    (RelativeDimensionLE ((W.inverseImage (pullback.fst f g)).ι ≫ (pullback.snd f g)) d ∧
      ∀ U : OpenSubspace (pullback f g), RelativeDimensionLE (U.ι ≫ (pullback.snd f g)) d →
        U.pointsSet ⊆ (W.inverseImage (pullback.fst f g)).pointsSet) :=
  sorry

/-- If `W` is a largest open source subspace on which `f` has relative dimension
at most `d`, then the points of `W` are exactly the points at which `f` has
relative dimension at most `d`. -/
theorem isLargestSourceOpen_relativeDimensionLE_pointsSet {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f] (d : ℕ)
    (W : OpenSubspace X) (hW : (RelativeDimensionLE (W.ι ≫ f) d ∧
      ∀ U : OpenSubspace X, RelativeDimensionLE (U.ι ≫ f) d →
        U.pointsSet ⊆ W.pointsSet)) :
    W.pointsSet = fiberDimensionLELocus f d :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
