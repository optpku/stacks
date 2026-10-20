/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.CupProduct

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory ComplexShape
open DerivedCategory.DerivedTensor.Right.Monoidal

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham

variable {X S : Scheme.{u}} (p : X ⟶ S)

/- The historical import retains the coefficient categories and the explicit tensor model used by
downstream cup-product constructions. -/
#check coefficientRing p
#check coefficientModules p
#check coefficientDerived p
#check @CoefficientTensorModel

/- The historical Chapter 50 import exposes the relative de Rham complex and its derived global
sections object from their reusable mathematical owner. -/
#check deRhamComplex p
#check (extendedDeRhamComplex p : CochainComplex
  (RingedSite.ModuleCat.{u} (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)) ℤ)

#check extendedWedge p
#check globalDerivedFunctor p
#check (globalDerivedObject p : coefficientDerived p)

/- The compatibility surface retains the complete type of the degreewise cup product. -/
#check (cohomologyCupProduct :
  (p : X ⟶ S) →
  [MonoidalCategory (coefficientDerived p)] →
  [(DerivedCategory.Qh : HomotopyCategory (coefficientModules p) (up ℤ) ⥤
    coefficientDerived p).Monoidal] →
  [(globalDerivedFunctor p).LaxMonoidal] →
  (i j : ℤ) →
    cohomology p i ⊗ cohomology p j ⟶ cohomology p (i + j))

/- The standard-presentation derived cohomology product retains its historical explicit argument
order for direct callers. -/
#check @CategoryTheory.derivedCohomologyProduct

end AlgebraicGeometry.Scheme.DeRham
