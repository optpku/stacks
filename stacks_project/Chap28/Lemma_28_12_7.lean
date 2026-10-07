module

public import ReasLib.AlgebraicGeometry.Scheme.CohenMacaulay.Normal
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 28.12.7: a locally Noetherian normal scheme of topological Krull dimension at most two
is Cohen–Macaulay. -/
@[stacks 0B3D] #check
  (AlgebraicGeometry.Scheme.cohenMacaulay_of_isNormal_of_topologicalKrullDim_le_two :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsLocallyNoetherian X],
      X.isNormal → topologicalKrullDim X ≤ 2 → AlgebraicGeometry.Scheme.CohenMacaulay X)
