module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.QuasiCompact
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiCompact.DominantBaseChange

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.QuasiCompactAndDominant

/-- Quasi-compactness together with dominance of scheme morphisms is local on
the target for the fpqc precoverage. -/
instance isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      ((@AlgebraicGeometry.QuasiCompact ⊓ @AlgebraicGeometry.IsDominant) :
        MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage := sorry

end AlgebraicGeometry.QuasiCompactAndDominant
