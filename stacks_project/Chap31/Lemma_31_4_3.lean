module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.EmbeddedPoints.Serre

open AlgebraicGeometry

universe u

/- Lemma 31.4.3: a coherent module on a locally Noetherian scheme has no embedded associated
points if and only if it satisfies Serre's condition `(S_1)`. -/
@[stacks 0346] #check
  (AlgebraicGeometry.Scheme.Modules.embeddedAssociatedPoints_eq_empty_iff_satisfiesSerreConditionS_one :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X] (ℱ : X.Modules) [ℱ.IsCoherent],
      ℱ.embeddedAssociatedPoints = (∅ : Set X) ↔
        AlgebraicGeometry.Scheme.Modules.satisfiesSerreConditionS ℱ 1)
