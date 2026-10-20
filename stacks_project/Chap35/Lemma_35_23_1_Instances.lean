module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.QuasiCompact

@[expose] public section

universe u

open CategoryTheory

#check (AlgebraicGeometry.QuasiCompact.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.QuasiCompact : MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage)
