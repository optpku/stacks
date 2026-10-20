module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Deformation.Parameters

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.Deformation

/-- The canonical relative-differentials sheaf of a morphism of algebraic spaces. -/
abbrev relativeDifferentialsOver {S : Scheme.{u}} {I U : AlgebraicSpace S}
    (p : I ⟶ U) : I.Modules := Hom.relativeDifferentials p

end AlgebraicGeometry.AlgebraicSpace.Hom.Deformation

/- 106.6.8.1: The internal-Hom module of differential parameters. -/
#check (AlgebraicGeometry.AlgebraicSpace.Hom.Deformation.parameterModule :
  ∀ {S : Scheme.{u}} {U U' I : AlgebraicSpace S}
    (iU : U ⟶ U') (p : I ⟶ U) (Δ : U ⟶ I) [IsFirstOrderThickening iU],
    RingedSite.ModuleCat.{u + 1} (commRingedSiteLift U))
