module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Resolution.EmbeddedCurve
import StacksCheckRecall

@[expose] public section

open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/- Lemma 54.15.2: if `Y` is an integral one-dimensional closed subscheme of a Noetherian
scheme and its normalization morphism is finite, then some finite sequence of blowups of the
ambient scheme at closed points has regular iterated strict transform of `Y`. -/
@[stacks 0BI5]
#check
  (AlgebraicGeometry.Scheme.existsRegularStrictTransformAfterPointBlowups :
    ∀ (X : Scheme.{u}) [IsNoetherian X] (Y : X.IdealSheafData)
      [IsIntegral Y.subscheme]
      (h_dim : topologicalKrullDim Y.subscheme = 1)
      [IsFinite (normalizationToOfIsNoetherian Y.subscheme)],
    ∃ (Xn : Scheme.{u}) (s : PointBlowupSequence X Xn),
      Regular (s.strictTransform Y.subschemeι))

end AlgebraicGeometry.Scheme
