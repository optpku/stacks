/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.StrictTransform.PointBlowupSequence
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Resolution.Curve
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Noetherian

@[expose] public section

open TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- An integral one-dimensional closed subscheme with finite normalization becomes regular after
finitely many blowups of the ambient scheme at closed points. -/
theorem existsRegularStrictTransformAfterPointBlowups
    (X : Scheme.{u}) [IsNoetherian X] (Y : X.IdealSheafData)
    [IsIntegral Y.subscheme] (h_dim : topologicalKrullDim Y.subscheme = 1)
    [IsFinite (normalizationToOfIsNoetherian Y.subscheme)] :
    ∃ (Xn : Scheme.{u}) (s : PointBlowupSequence X Xn),
      Regular (s.strictTransform Y.subschemeι) := sorry

/-- A finite family of distinct integral one-dimensional closed subschemes of a Noetherian scheme
with finite normalization admits one finite sequence of blowups at closed points whose
strict transforms are regular and pairwise disjoint. -/
theorem existsDisjointRegularStrictTransforms
    (X : Scheme.{u}) [IsNoetherian X] (n : ℕ) (Y : Fin n → X.IdealSheafData)
    (h_distinct : Function.Injective Y)
    [∀ i, IsIntegral (Y i).subscheme]
    (h_dim : ∀ i, topologicalKrullDim (Y i).subscheme = 1)
    [∀ i, IsFinite (normalizationToOfIsNoetherian (Y i).subscheme)] :
    ∃ (Xn : Scheme.{u}) (s : PointBlowupSequence X Xn),
      (∀ i, Regular (s.strictTransform (Y i).subschemeι)) ∧
        Pairwise (fun i j ↦
          Disjoint (Set.range (s.strictTransformToTarget (Y i).subschemeι))
            (Set.range (s.strictTransformToTarget (Y j).subschemeι))) := sorry

end AlgebraicGeometry.Scheme
