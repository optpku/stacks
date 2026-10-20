module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.Algebra.Total
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.Symmetric.Lift
public import ReasLib.RingTheory.Ideal.AssociatedGraded.Conormal

/-!
# Symmetric algebra comparison for conormal algebras

The degree-one classes in the conormal algebra of an immersion induce a canonical morphism
from the symmetric algebra of the conormal sheaf to the total conormal algebra.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ConormalAlgebra

variable {X Z : Scheme.{u}}

/-- On an open of the source of an immersion, the sectionwise conormal module maps to the
degree-one summand of the total conormal algebra. -/
noncomputable def degreeOnePresheafApp (i : Z ⟶ X) [IsImmersion i]
    (U : (Opens Z)ᵒᵖ) :
    (conormalPresheaf
        (RingedSpace.Hom.inverseImageStructureSheafHomComm i.toShHom)).obj U ⟶
      ((restrictionAlong
          (RingedSpace.Hom.inverseImageStructureSheafHomComm i.toShHom)).obj
        (QcAlgebraUnder.underlyingModule Z (total i))).val.obj U := by
  let α := RingedSpace.Hom.inverseImageStructureSheafHomComm i.toShHom
  let I := KernelIdeal.sectionIdeal α U
  let gradeToExtended :
      KernelIdeal.AssociatedGraded.gradeObj α 1 U ⟶
        (ModuleCat.restrictScalars (α.hom.app U).hom).obj
          (KernelIdeal.AssociatedGraded.obj α 1 U) :=
    (ModuleCat.extendRestrictScalarsAdj (α.hom.app U).hom).unit.app
      (KernelIdeal.AssociatedGraded.gradeObj α 1 U)
  let extendedToSheaf :
      KernelIdeal.AssociatedGraded.obj α 1 U ⟶
        ((ConormalAlgebra i).obj 1).val.obj U :=
    (moduleSheafificationUnitToVal Z.sheaf
      (KernelIdeal.AssociatedGraded.presheaf.{u, u} α 1)).app U
  let degreeOne :
      ModuleCat.of
          (((TopCat.Sheaf.pullback CommRingCat.{u} i.toShHom.hom.base).obj
            X.sheaf).obj.obj U) I.Cotangent ⟶
        KernelIdeal.AssociatedGraded.gradeObj α 1 U :=
    ModuleCat.ofHom (idealConormalDegreeOne I)
  exact
    degreeOne ≫
      gradeToExtended ≫
      (ModuleCat.restrictScalars (α.hom.app U).hom).map extendedToSheaf ≫
      (ModuleCat.restrictScalars (α.hom.app U).hom).map
        ((Sigma.ι (ConormalAlgebra i).toGradedObject 1).val.app U) ≫
      (ModuleCat.restrictScalars (α.hom.app U).hom).map
        ((totalUnderlyingModuleIso i).hom.val.app U)

/-- On a cotangent generator, the sectionwise degree-one map is the homogeneous degree-one
class followed by scalar extension, sheafification, and inclusion into the total algebra. -/
theorem degreeOnePresheafApp_toCotangent (i : Z ⟶ X) [IsImmersion i]
    (U : (Opens Z)ᵒᵖ)
    (x : KernelIdeal.sectionIdeal
      (RingedSpace.Hom.inverseImageStructureSheafHomComm i.toShHom) U) :
    let α := RingedSpace.Hom.inverseImageStructureSheafHomComm i.toShHom
    let I := KernelIdeal.sectionIdeal α U
    let gradeToTotal :
        KernelIdeal.AssociatedGraded.gradeObj α 1 U ⟶
          ((restrictionAlong α).obj
            (QcAlgebraUnder.underlyingModule Z (total i))).val.obj U :=
      (ModuleCat.extendRestrictScalarsAdj (α.hom.app U).hom).unit.app
          (KernelIdeal.AssociatedGraded.gradeObj α 1 U) ≫
        (ModuleCat.restrictScalars (α.hom.app U).hom).map
          ((moduleSheafificationUnitToVal Z.sheaf
            (KernelIdeal.AssociatedGraded.presheaf.{u, u} α 1)).app U) ≫
        (ModuleCat.restrictScalars (α.hom.app U).hom).map
          ((Sigma.ι (ConormalAlgebra i).toGradedObject 1).val.app U) ≫
        (ModuleCat.restrictScalars (α.hom.app U).hom).map
          ((totalUnderlyingModuleIso i).hom.val.app U)
    degreeOnePresheafApp i U (I.toCotangent x) =
      gradeToTotal
        ⟨Ideal.AssociatedGraded.degreeOne x,
          Ideal.AssociatedGraded.degreeOne_mem_grade x⟩ := sorry

/-- The sectionwise degree-one maps commute with restriction of open sets. -/
theorem degreeOnePresheafApp_naturality (i : Z ⟶ X) [IsImmersion i]
    {U V : (Opens Z)ᵒᵖ} (f : U ⟶ V) :
    let α := RingedSpace.Hom.inverseImageStructureSheafHomComm i.toShHom
    (conormalPresheaf α).map f ≫
        (ModuleCat.restrictScalars
          (((TopCat.Sheaf.pullback CommRingCat.{u} i.toShHom.hom.base).obj
            X.sheaf).obj.map f).hom).map
          (degreeOnePresheafApp i V) =
      degreeOnePresheafApp i U ≫
        ((restrictionAlong α).obj
          (QcAlgebraUnder.underlyingModule Z (total i))).val.map f := sorry

/-- The natural transformation on conormal presheaves obtained from the sectionwise degree-one
maps. -/
@[no_expose] noncomputable def degreeOnePresheafHom (i : Z ⟶ X) [IsImmersion i] :
    let α := RingedSpace.Hom.inverseImageStructureSheafHomComm i.toShHom
    conormalPresheaf.{u} α ⟶
      ((restrictionAlong α).obj (QcAlgebraUnder.underlyingModule Z (total i))).val :=
  { app := degreeOnePresheafApp i
    naturality := fun {_ _} f ↦ degreeOnePresheafApp_naturality i f }

/-- Sheafifying the degree-one presheaf map gives a map over the source structure sheaf. -/
@[no_expose] noncomputable def degreeOneOverSource (i : Z ⟶ X) [IsImmersion i] :
    let α := RingedSpace.Hom.inverseImageStructureSheafHomComm i.toShHom
    conormalSourceOverSource.{u} α ⟶
      (restrictionAlong α).obj (QcAlgebraUnder.underlyingModule Z (total i)) :=
  (moduleSheafificationHomEquiv
    ((TopCat.Sheaf.pullback CommRingCat.{u} i.toShHom.hom.base).obj X.sheaf)
    (conormalPresheaf.{u}
      (RingedSpace.Hom.inverseImageStructureSheafHomComm i.toShHom))
    ((restrictionAlong
      (RingedSpace.Hom.inverseImageStructureSheafHomComm i.toShHom)).obj
        (QcAlgebraUnder.underlyingModule Z (total i)))).symm
    (degreeOnePresheafHom i)

/-- The conormal sheaf maps canonically to the module underlying the total conormal algebra by
placing cotangent classes in degree one. -/
noncomputable def degreeOneToTotal (i : Z ⟶ X) [IsImmersion i] :
    Hom.conormalSheaf i ⟶ QcAlgebraUnder.underlyingModule Z (total i) :=
  ((extendRestrictAdj
    (RingedSpace.Hom.inverseImageStructureSheafHomComm i.toShHom)).homEquiv
      (conormalSourceOverSource.{u}
        (RingedSpace.Hom.inverseImageStructureSheafHomComm i.toShHom))
      (QcAlgebraUnder.underlyingModule Z (total i))).symm
    (degreeOneOverSource i)

/-- The symmetric algebra of the conormal sheaf maps canonically to the total conormal
algebra. -/
noncomputable def symmetricToTotal (i : Z ⟶ X) [IsImmersion i] :
    SymmetricAlgebra.qcAlgebra (Hom.conormalSheaf i) ⟶ total i :=
  SymmetricAlgebra.lift (Hom.conormalSheaf i) (total i) (degreeOneToTotal i)

/-- The symmetric-to-total conormal algebra map restricts on degree-one generators to the
canonical inclusion of the conormal sheaf into the total conormal algebra. -/
theorem symmetricToTotal_ι (i : Z ⟶ X) [IsImmersion i] :
    SymmetricAlgebra.ι (Hom.conormalSheaf i) ≫
        QcAlgebraUnder.underlyingModuleMap Z (symmetricToTotal i) =
      degreeOneToTotal i := sorry

end AlgebraicGeometry.Scheme.ConormalAlgebra
