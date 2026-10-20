module

public import ReasLib.AlgebraicGeometry.Scheme.SerreCondition.Normal
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 28.12.5: a locally Noetherian scheme is normal if and only if it satisfies Serre's
conditions `(S₂)` and `(R₁)`. -/
@[stacks 0345] #check
  (AlgebraicGeometry.Scheme.isNormal_iff_serre :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsLocallyNoetherian X],
      X.isNormal ↔
        AlgebraicGeometry.Scheme.satisfiesSerreConditionS X 2 ∧
          AlgebraicGeometry.Scheme.satisfiesSerreConditionR X 1)
