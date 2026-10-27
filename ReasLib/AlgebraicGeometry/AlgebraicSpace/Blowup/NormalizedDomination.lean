/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.NormalizedSequence
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Nagata
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Birational

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A proper birational morphism to a two-dimensional Noetherian Nagata algebraic space is
dominated by a finite sequence of normalized blowups at closed points, beginning with the
canonical normalization of the target. -/
theorem existsNormalizedBlowupSequence_lift {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} [IsNoetherian X] [IsNagata X] [IsDecent Y]
    [HasFiniteIrreducibleComponents X] [HasFiniteIrreducibleComponents Y]
    (f : Y ⟶ X) [Proper f] [IsBirational f] (h_dim : dimension X = 2) :
    ∃ (Z : AlgebraicSpace S) (s : NormalizedBlowupSequence X.normalization Z)
      (g : Z ⟶ Y), g ≫ f = s.toSource ≫ X.normalizationTo :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
