/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.HodgeFiltration

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham

variable {X S : Scheme.{u}} (f : X ⟶ S) (n p : ℤ)

/- This typed compatibility bridge preserves the historical Chapter 50 import surface. -/
#check (cohomology f n :
  ModuleCat.{u} (RingedSite.Hom.globalSectionsRing
    (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom)))

#check (hodgeMap f p n :
  @Functor.RightDerived.Homotopy.cochainCohomology
      _ inferInstance inferInstance
      (RingedSite.Hom.moduleCat_hasDerivedCategory.{u, u, u, u}
        (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom))
      _ inferInstance inferInstance
      (ModuleCat.hasDerivedCategory (RingedSite.Hom.globalSectionsRing
        (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom)))
      (RingedSite.Hom.moduleGlobalSectionsFunctor.{u}
        (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom))
      (RingedSite.Hom.moduleGlobalSectionsFunctor_additive.{u, u, u, u}
        (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom))
      (RingedSite.Hom.moduleGlobalSectionsToModuleDerived_hasRightDerivedFunctor.{u, u, u, u}
        (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom))
      (CochainComplex.Brutal.Stage.obj
        ((RingedSpace.DeRham.complex f.toLRSHom.toShHom).extend embeddingUpNat) p) n ⟶
    cohomology f n)

#check (hodgeFiltration f n : DecreasingFiltration (cohomology f n))

end AlgebraicGeometry.Scheme.DeRham
