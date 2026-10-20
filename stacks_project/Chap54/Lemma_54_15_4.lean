/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Resolution.EmbeddedCurve
import StacksCheckRecall

@[expose] public section

open TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/- Lemma 54.15.4: a finite family of distinct integral one-dimensional closed subschemes of a
Noetherian scheme whose normalization morphisms are finite admits a finite sequence of
blowups at closed points such that the final strict transforms are regular and pairwise
disjoint. Distinctness is implicit in the source proof's use of finite intersection
multiplicities, whose setup excludes the generic point of one curve from the other. -/
@[stacks 0BI8]
#check
  (AlgebraicGeometry.Scheme.existsDisjointRegularStrictTransforms :
    ∀ (X : Scheme.{u}) [IsNoetherian X] (n : ℕ) (Y : Fin n → X.IdealSheafData)
      (h_distinct : Function.Injective Y)
      [∀ i, IsIntegral (Y i).subscheme]
      (h_dim : ∀ i, topologicalKrullDim (Y i).subscheme = 1)
      [∀ i, IsFinite (normalizationToOfIsNoetherian (Y i).subscheme)],
    ∃ (Xn : Scheme.{u}) (s : PointBlowupSequence X Xn),
      (∀ i, Regular (s.strictTransform (Y i).subschemeι)) ∧
        Pairwise (fun i j ↦
          Disjoint (Set.range (s.strictTransformToTarget (Y i).subschemeι))
            (Set.range (s.strictTransformToTarget (Y j).subschemeι))))

end AlgebraicGeometry.Scheme
