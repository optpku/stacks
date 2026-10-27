/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeDimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.CohenMacaulay
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Support

/-! # Clopen relative-dimension decomposition of Cohen–Macaulay morphisms -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A locally finitely presented Cohen–Macaulay morphism of algebraic spaces admits
a pairwise disjoint clopen cover of its source indexed by natural numbers, with
relative dimension `d` on the `d`-th open subspace. -/
theorem exists_clopen_relativeDimension_decomposition
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] [CohenMacaulay f] :
    ∃ U : ℕ → OpenSubspace X,
      (⋃ d, (U d).pointsSet) = Set.univ ∧
        Pairwise (fun d e ↦ Disjoint (U d).pointsSet (U e).pointsSet) ∧
        (∀ d, IsClopen (U d).pointsSet) ∧
        ∀ d, RelativeDimension ((U d).ι ≫ f) d :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
