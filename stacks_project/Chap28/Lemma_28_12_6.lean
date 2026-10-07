module

public import ReasLib.AlgebraicGeometry.Scheme.Normal.Regular
import StacksCheckRecall

@[expose] public section

universe u

/-
Lemma 28.12.6: A locally Noetherian normal scheme of dimension at most one is regular.
-/
@[stacks 0BX2] #check
  (AlgebraicGeometry.Scheme.regular_of_isNormal_of_topologicalKrullDim_le_one :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsLocallyNoetherian X],
      X.isNormal → topologicalKrullDim X ≤ 1 → AlgebraicGeometry.Scheme.Regular X)

end
