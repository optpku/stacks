/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor.CohomologyProduct
public import ReasLib.Algebra.Homology.Embedding.UpNatMonoidal
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived
public import ReasLib.AlgebraicGeometry.RingedSpace.DeRham.Wedge
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.HodgeFiltration
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Homotopy.Cohomology
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric

/-!
# Cup products on relative de Rham cohomology

The wedge product on the relative de Rham complex induces a degreewise product on derived global
sections. The derived-category presentation is fixed explicitly to the canonical module model.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory ComplexShape
open DerivedCategory.DerivedTensor.Right.Monoidal Functor.RightDerived.Homotopy
open scoped DerivedTensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham

variable {X S : Scheme.{u}}

/-- The ring of global sections of the coefficient ringed site of a scheme morphism. -/
abbrev coefficientRing (p : X ⟶ S) :=
  RingedSite.Hom.globalSectionsRing
    (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom)

/-- The category of modules over the global coefficient ring of a scheme morphism. -/
abbrev coefficientModules (p : X ⟶ S) := ModuleCat.{u} (coefficientRing p)

/-- The canonical derived category of modules over the global coefficient ring. -/
abbrev coefficientDerived (p : X ⟶ S) := DerivedCategory (coefficientModules p)

/-- The coefficient ring is commutative because it is the ring of global sections of a sheaf of
commutative rings. -/
noncomputable instance coefficientGlobalSectionsCommRing (p : X ⟶ S) :
    CommRing (coefficientRing p) :=
  { (inferInstance : Ring (coefficientRing p)) with
    mul_comm := sorry }

/-- Coefficient modules carry their canonical tensor-product monoidal structure. -/
noncomputable instance coefficientModuleMonoidalCategory (p : X ⟶ S) :
    MonoidalCategory (coefficientModules p) :=
  ModuleCat.monoidalCategory

/-- The canonical tensor product of coefficient modules is additive in both variables. -/
noncomputable instance coefficientModuleMonoidalPreadditive (p : X ⟶ S) :
    MonoidalPreadditive (coefficientModules p) :=
  ModuleCat.instMonoidalPreadditive

/-- Coefficient modules carry the canonical tensor symmetry. -/
noncomputable instance coefficientModuleBraidedCategory (p : X ⟶ S) :
    BraidedCategory (coefficientModules p) :=
  ModuleCat.MonoidalCategory.instBraidedCategory

/-- An explicit comparison model for the right-derived tensor product over the global coefficient
ring. -/
abbrev CoefficientTensorModel (p : X ⟶ S)
    [MonoidalCategory (coefficientDerived p)] :=
  Model (C := coefficientModules p)

/-- The canonical tensor model supplied by the strong monoidal localization. -/
noncomputable def coefficientTensorModel (p : X ⟶ S)
    [MonoidalCategory (coefficientDerived p)]
    [(DerivedCategory.Qh : HomotopyCategory (coefficientModules p) (up ℤ) ⥤
      coefficientDerived p).Monoidal] :
    CoefficientTensorModel p :=
  DerivedCategory.DerivedTensor.Right.Monoidal.Strong.modelFamily

/-- The relative de Rham complex before extension from nonnegative to integer degrees. -/
noncomputable abbrev deRhamComplex (p : X ⟶ S) :=
  RingedSpace.DeRham.complex p.toLRSHom.toShHom

/-- The relative de Rham complex extended by zero to integer degrees. -/
noncomputable abbrev extendedDeRhamComplex (p : X ⟶ S) :=
  (deRhamComplex p).extend embeddingUpNat

/-- The wedge multiplication on the relative de Rham complex after extension to integer degrees. -/
noncomputable def extendedWedge (p : X ⟶ S) :
    HomologicalComplex.tensorObj (extendedDeRhamComplex p) (extendedDeRhamComplex p) ⟶
      extendedDeRhamComplex p :=
  embeddingUpNat.extendTensorHom (deRhamComplex p) (deRhamComplex p) ≫
    (embeddingUpNat.extendFunctor _).map
      (RingedSpace.DeRham.wedge p.toLRSHom.toShHom)

/-- The total right-derived global-sections functor on coefficient-module cochain complexes, with
its source and target derived-category presentations fixed explicitly. -/
noncomputable abbrev globalDerivedFunctor (p : X ⟶ S) :=
  @cochainFunctor
    (RingedSite.ModuleCat.{u} (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom))
      inferInstance inferInstance
      (RingedSite.Hom.moduleCat_hasDerivedCategory.{u, u, u, u}
        (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom))
    (coefficientModules p) inferInstance inferInstance
      (ModuleCat.hasDerivedCategory (coefficientRing p))
    (RingedSite.Hom.moduleGlobalSectionsFunctor.{u}
      (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom))
    (RingedSite.Hom.moduleGlobalSectionsFunctor_additive.{u, u, u, u}
      (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom))
    (RingedSite.Hom.moduleGlobalSectionsToModuleDerived_hasRightDerivedFunctor.{u, u, u, u}
      (RingedSpace.DeRham.coefficientSite p.toLRSHom.toShHom))

/-- The derived global-sections object of the integer-extended relative de Rham complex. -/
noncomputable abbrev globalDerivedObject (p : X ⟶ S) :=
  (globalDerivedFunctor p).obj (extendedDeRhamComplex p)

/-- The degreewise relative de Rham cup product induced by derived global sections and wedge
multiplication. -/
noncomputable def cohomologyCupProduct (p : X ⟶ S)
    [MonoidalCategory (coefficientDerived p)]
    [(DerivedCategory.Qh : HomotopyCategory (coefficientModules p) (up ℤ) ⥤
      coefficientDerived p).Monoidal]
    [(globalDerivedFunctor p).LaxMonoidal]
    (i j : ℤ) :
    cohomology p i ⊗ cohomology p j ⟶ cohomology p (i + j) :=
  CategoryTheory.derivedCohomologyProductWith
      (hD := ModuleCat.hasDerivedCategory (coefficientRing p))
      (coefficientTensorModel p) i j
      (globalDerivedObject p) (globalDerivedObject p) ≫
    (DerivedCategory.homologyFunctor (coefficientModules p) (i + j)).map
      (((coefficientTensorModel p).tensorIsoObj
          (globalDerivedObject p) (globalDerivedObject p)).inv ≫
        Functor.LaxMonoidal.μ (globalDerivedFunctor p)
            (extendedDeRhamComplex p) (extendedDeRhamComplex p) ≫
          (globalDerivedFunctor p).map (extendedWedge p))

/-- The relative de Rham cup product is associative, with the canonical reassociation of degrees. -/
theorem cohomologyCupProduct_assoc (p : X ⟶ S)
    [MonoidalCategory (coefficientDerived p)]
    [(DerivedCategory.Qh : HomotopyCategory (coefficientModules p) (up ℤ) ⥤
      coefficientDerived p).Monoidal]
    [(globalDerivedFunctor p).LaxMonoidal]
    (i j k : ℤ) :
    (cohomologyCupProduct p i j ▷ cohomology p k) ≫
        cohomologyCupProduct p (i + j) k =
      (α_ (cohomology p i) (cohomology p j) (cohomology p k)).hom ≫
        (cohomology p i ◁ cohomologyCupProduct p j k) ≫
        cohomologyCupProduct p i (j + k) ≫
        eqToHom (congrArg (cohomology p) (add_assoc i j k).symm) := sorry

/-- The relative de Rham cup product is graded commutative with its Koszul sign. -/
theorem cohomologyCupProduct_gradedComm (p : X ⟶ S)
    [MonoidalCategory (coefficientDerived p)] [BraidedCategory (coefficientDerived p)]
    [(DerivedCategory.Qh : HomotopyCategory (coefficientModules p) (up ℤ) ⥤
      coefficientDerived p).Braided]
    [(globalDerivedFunctor p).LaxBraided]
    (i j : ℤ) :
    cohomologyCupProduct p i j =
      (i * j).negOnePow •
        ((β_ (cohomology p i) (cohomology p j)).hom ≫
          cohomologyCupProduct p j i ≫
          eqToHom (congrArg (cohomology p) (add_comm j i))) := sorry

end AlgebraicGeometry.Scheme.DeRham
