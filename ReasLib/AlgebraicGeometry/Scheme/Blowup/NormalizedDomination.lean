/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.NormalizedSequence
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.GenericPoints
public import ReasLib.AlgebraicGeometry.Scheme.Normal.Nagata.Basic

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A proper birational morphism to a two-dimensional Noetherian Nagata scheme is dominated by a
finite sequence of normalized blowups at closed points, beginning with the normalization of the
target. -/
theorem exists_normalizedBlowupSequence_lift {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsNoetherian X] [Scheme.Nagata X] [IsProper f] [IsBirational f]
    (h_dim : topologicalKrullDim X = 2) :
    ∃ (Z : Scheme.{u}) (s : Scheme.NormalizedBlowupSequence X.normalization Z)
      (g : Z ⟶ Y), g ≫ f = s.toSource ≫ X.normalizationTo := sorry

end AlgebraicGeometry.Scheme.Hom
