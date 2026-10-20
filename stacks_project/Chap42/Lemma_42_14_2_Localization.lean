module

public import ReasLib.AlgebraicGeometry.CycleGroup.Localization

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Opens

variable {X : Scheme.{u}}

/-- The defining ideal of the canonical reduced closed complement of an open subscheme. -/
noncomputable abbrev reducedComplement (U : X.Opens) : X.IdealSheafData :=
  (ClosedSubschemeStructure.reduced U.compl).ideal

end AlgebraicGeometry.Scheme.Opens
