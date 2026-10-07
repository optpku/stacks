module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.GaussManin.DifferentialGraded

@[expose] public section

open AlgebraicGeometry CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham

/- This compatibility module retains the established import path for the relative de Rham DGA. -/
#check (gaussManinDeRhamDGA :
  {Y S : Scheme.{u}} → (b : Y ⟶ S) →
    @DifferentialGradedAlgebra.{u, u, u} _ _ (Opens.grothendieckTopology Y)
      _ _ _ (RingedSpace.DeRham.coefficients b.toLRSHom.toShHom))

end AlgebraicGeometry.Scheme.DeRham
