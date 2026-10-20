/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom.FinitePresentation

/-- A flat finitely presented morphism with geometrically reduced fibres and a finite locally
free multisection meeting a geometrically connected fibre admits a quasi-compact source open
containing that fibre whose nonempty fibres are geometrically connected. -/
theorem exists_compactOpen_geometricallyConnectedFibers {Z X Y : Scheme.{u}}
    (σ : Z ⟶ X) (f : X ⟶ Y) (y : Y) [FinitePresentation f] [Flat f]
    [IsFiniteLocallyFree (σ ≫ f)] (hZy : Nonempty ((σ ≫ f).fiber y))
    [GeometricallyReduced f] [GeometricallyConnected (f.fiberToSpecResidueField y)] :
    ∃ U : X.Opens, IsCompact (U : Set X) ∧ f ⁻¹' {y} ⊆ U ∧
      ∀ y' : Y, Nonempty ((U.ι ≫ f).fiber y') →
        GeometricallyConnected ((U.ι ≫ f).fiberToSpecResidueField y') := sorry

end AlgebraicGeometry.Scheme.Hom.FinitePresentation
