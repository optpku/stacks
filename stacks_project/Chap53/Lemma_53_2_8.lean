/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.SmoothModels
import StacksCheckRecall

universe u

/- Lemma 53.2.8: over a perfect field, the curve underlying a nonsingular projective
model is smooth. -/
@[stacks 0BY3] #check
  (AlgebraicGeometry.NonsingularProjectiveModel.WithIso.smooth_of_perfectField :
    ∀ {k : Type u} [Field k] [PerfectField k]
    {X : AlgebraicGeometry.SchemeOverField k} [AlgebraicGeometry.Curve X]
    (Y : AlgebraicGeometry.NonsingularProjectiveModel.WithIso X),
    AlgebraicGeometry.Smooth Y.curve.hom)
