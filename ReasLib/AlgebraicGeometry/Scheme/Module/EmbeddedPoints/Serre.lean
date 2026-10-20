module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Depth
public import ReasLib.AlgebraicGeometry.Scheme.Module.EmbeddedPoints
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Serre

/-!
# Embedded associated points and Serre's condition

For a coherent module on a locally Noetherian scheme, Serre's condition
`(S_1)` is equivalent to the absence of embedded associated points.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- A coherent module on a locally Noetherian scheme has no embedded associated
points if and only if it satisfies Serre's condition `(S_1)`. -/
theorem embeddedAssociatedPoints_eq_empty_iff_satisfiesSerreConditionS_one
    (ℱ : X.Modules) [ℱ.IsCoherent] :
    ℱ.embeddedAssociatedPoints = (∅ : Set X) ↔ satisfiesSerreConditionS ℱ 1 := sorry

end AlgebraicGeometry.Scheme.Modules
