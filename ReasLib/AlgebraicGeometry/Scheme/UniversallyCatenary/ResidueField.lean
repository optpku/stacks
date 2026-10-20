module

public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary.Affine
public import ReasLib.RingTheory.Catenary.Field
public import Mathlib.AlgebraicGeometry.Noetherian

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/-- The spectrum of the residue field of a scheme point is universally catenary. -/
instance instUniversallyCatenary_specResidueField {X : Scheme.{u}} (x : X) :
    UniversallyCatenary (Spec (X.residueField x)) := sorry

/-- The spectrum of a residue field is locally Noetherian. -/
instance instIsLocallyNoetherian_specResidueField {X : Scheme.{u}} (x : X) :
    IsLocallyNoetherian (Spec (X.residueField x)) := sorry

end AlgebraicGeometry
