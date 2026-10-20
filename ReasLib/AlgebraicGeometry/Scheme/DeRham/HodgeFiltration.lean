module

public import ReasLib.Algebra.Homology.CochainComplex.Truncation.Brutal
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived
public import ReasLib.AlgebraicGeometry.RingedSpace.DeRham.Map
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Homotopy.Cohomology
public import ReasLib.CategoryTheory.Filtration.Indexed
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Subobject.Limits

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham

variable {X S : Scheme.{u}}

/-- Relative de Rham cohomology in degree `n` is the derived module-valued global sections of the
integer extension of the relative de Rham complex. -/
noncomputable abbrev cohomology (f : X ⟶ S) (n : ℤ) :=
  @Functor.RightDerived.Homotopy.cochainCohomology
    (RingedSite.ModuleCat.{u} (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom)) inferInstance
      inferInstance
      (RingedSite.Hom.moduleCat_hasDerivedCategory.{u, u, u, u}
        (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom))
    (ModuleCat.{u} (RingedSite.Hom.globalSectionsRing
      (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom))) inferInstance inferInstance
      (ModuleCat.hasDerivedCategory (RingedSite.Hom.globalSectionsRing
        (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom)))
    (RingedSite.Hom.moduleGlobalSectionsFunctor.{u}
      (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom))
    (RingedSite.Hom.moduleGlobalSectionsFunctor_additive.{u, u, u, u}
      (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom))
    (RingedSite.Hom.moduleGlobalSectionsToModuleDerived_hasRightDerivedFunctor.{u, u, u, u}
      (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom))
    ((RingedSpace.DeRham.complex f.toLRSHom.toShHom).extend embeddingUpNat) n

/-- The Hodge map is induced on cohomology by the inclusion of the brutal truncation at `p` into
the full relative de Rham complex. -/
noncomputable abbrev hodgeMap (f : X ⟶ S) (p n : ℤ) :
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
      cohomology f n :=
  @Functor.RightDerived.Homotopy.cochainCohomologyMap
    (RingedSite.ModuleCat.{u} (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom)) inferInstance
      inferInstance
      (RingedSite.Hom.moduleCat_hasDerivedCategory.{u, u, u, u}
        (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom))
    (ModuleCat.{u} (RingedSite.Hom.globalSectionsRing
      (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom))) inferInstance inferInstance
      (ModuleCat.hasDerivedCategory (RingedSite.Hom.globalSectionsRing
        (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom)))
    (RingedSite.Hom.moduleGlobalSectionsFunctor.{u}
      (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom))
    (RingedSite.Hom.moduleGlobalSectionsFunctor_additive.{u, u, u, u}
      (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom))
    (RingedSite.Hom.moduleGlobalSectionsToModuleDerived_hasRightDerivedFunctor.{u, u, u, u}
      (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom)) _ _
    (CochainComplex.Brutal.Stage.ι
      ((RingedSpace.DeRham.complex f.toLRSHom.toShHom).extend embeddingUpNat) p) n

/-- For `p ≤ q`, the Hodge map from cutoff `q` factors through the Hodge map from cutoff `p`. -/
theorem hodgeMap_factorization (f : X ⟶ S) {p q n : ℤ} (hpq : p ≤ q) :
    hodgeMap f q n =
      @Functor.RightDerived.Homotopy.cochainCohomologyMap
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
          (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom)) _ _
        (CochainComplex.Brutal.Stage.comparison
          ((RingedSpace.DeRham.complex f.toLRSHom.toShHom).extend embeddingUpNat) hpq) n ≫
        hodgeMap f p n := sorry

/-- The categorical images of the Hodge maps form an antitone family of subobjects. -/
theorem hodgeFiltration_antitone (f : X ⟶ S) (n : ℤ) :
    Antitone (fun p : ℤ ↦ imageSubobject (hodgeMap f p n)) := sorry

/-- The Hodge filtration on relative de Rham cohomology is the decreasing filtration whose stage
at `p` is the categorical image of `hodgeMap f p n`. -/
noncomputable def hodgeFiltration (f : X ⟶ S) (n : ℤ) :
    DecreasingFiltration (cohomology f n) where
  toFun p := imageSubobject (hodgeMap f p n)
  monotone' _ _ hpq := hodgeFiltration_antitone f n hpq

/-- The `p`-th stage of the Hodge filtration is the image of the hypercohomology map from the
brutally truncated relative de Rham complex. -/
theorem hodgeFiltration_stage (f : X ⟶ S) (n p : ℤ) :
    (hodgeFiltration f n).stage p = imageSubobject (hodgeMap f p n) := sorry

end AlgebraicGeometry.Scheme.DeRham
