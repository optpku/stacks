/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Characterization
import StacksCheckRecall

/-!
# Lemma 87.9.5

An fppf sheaf on `(Sch/S)_fppf` is an affine formal algebraic space if and only
if every map from an affine `S`-scheme factors through a representable
thickening from an affine `S`-scheme, and the coequalizer-of-representables
size condition of Remark 87.11.5 holds.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology

universe u

/- Lemma 87.9.5 -/
@[stacks 0AIB] #check
  (AlgebraicGeometry.IsAffineFormalAlgebraicSpace.iff_factorsThroughRepresentableAffineThickening :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      [HasWeakSheafify (AlgebraicGeometry.ChosenBigFppfSite.full.bigTopology S) (Type (u + 1))]
      [HasPullbacks
        (Sheaf (AlgebraicGeometry.ChosenBigFppfSite.full.bigTopology S) (Type (u + 1)))]
      (X : Sheaf (AlgebraicGeometry.ChosenBigFppfSite.full.bigTopology S) (Type (u + 1))),
      AlgebraicGeometry.IsAffineFormalAlgebraicSpace X ↔
        AlgebraicGeometry.IsAffineFormalAlgebraicSpace.factorsThroughRepresentableAffineThickening X ∧
          AlgebraicGeometry.ChosenBigFppfSite.IsCoequalizerOfRepresentables X)
