module

public import ReasLib.AlgebraicGeometry.Scheme.CohenMacaulay.SerreCondition
public import ReasLib.AlgebraicGeometry.Scheme.Dimension.Stalk
public import ReasLib.AlgebraicGeometry.Scheme.EmbeddedPoints
public import ReasLib.AlgebraicGeometry.Scheme.Module.EmbeddedPoints.Serre

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) [IsLocallyNoetherian X]

/-- A locally Noetherian scheme of topological Krull dimension at most one is Cohen-Macaulay
if and only if it has no embedded points. -/
theorem cohenMacaulay_iff_embeddedPoints_eq_empty_of_topologicalKrullDim_le_one
    (hdim : topologicalKrullDim X ≤ 1) :
    CohenMacaulay X ↔ X.embeddedPoints = (∅ : Set X) := sorry

end AlgebraicGeometry.Scheme
