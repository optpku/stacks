/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.TensorWithObject.Derived.Regular
public import ReasLib.Algebra.Homology.CochainDGAlgebra.DegreeZero.Functor
public import ReasLib.Algebra.Homology.CochainDGAlgebra.Hom.QuasiIso.Derived
public import ReasLib.Algebra.Homology.CochainDGAlgebra.Hom.Restriction.Derived.Adjunction
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorProduct.Derived.Unit
public import ReasLib.Algebra.Homology.DifferentialGradedModule.DegreeZero.Triangulated
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Beilinson.EndomorphismAlgebra
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Beilinson.Generation
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Comparison
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Closure

/-!
# The Beilinson equivalence for projective space

Derived tensoring with the degree-zero Beilinson generator identifies the derived category of
right modules over its graded-matrix endomorphism algebra with the derived category of modules
having quasicoherent cohomology on projective space.
-/

@[expose] public section

open CategoryTheory
open CochainComplex.HomComplex
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.TensorWithObject
open scoped ModuleCat.Algebra

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace.Beilinson

variable (A : Type u) [CommRing A] (n : ℕ)

/-- The degree-zero complex on the Beilinson generator. -/
noncomputable def complex :
    CochainComplex (scheme A n).Modules ℤ :=
  (CochainComplex.singleFunctor (scheme A n).Modules 0).obj
    (beilinsonGenerator A n)

/-- The Beilinson complex is the single complex concentrated in degree zero. -/
theorem complex_def :
    complex A n =
      (CochainComplex.singleFunctor (scheme A n).Modules 0).obj
        (beilinsonGenerator A n) := sorry

/-- Every homology sheaf of the Beilinson complex is quasicoherent. -/
theorem complex_homology_isQuasicoherent (i : ℤ) :
    RingedSpace.quasiCoherentModuleProperty (scheme A n).toRingedSpace
      ((complex A n).homology i) := sorry

/-- The Beilinson complex defines a compact object of the ambient derived category. -/
theorem complex_isCompact :
    IsCompactObject (DerivedCategory.Q.obj (complex A n)) := sorry

/-- Derived tensoring with the Beilinson complex has quasicoherent homology on every object. -/
theorem ambientTensorFunctor_mem
    (M : DifferentialGradedModule.Derived.Category.{0, u}
      (endDGA.{u, u} (complex A n))) :
    Scheme.ModuleDerived.quasicoherentProperty (scheme A n)
      ((SheafOfModules.RingedSite.TensorWithObject.Derived.tensorFunctor
        (complex A n)).obj M) := sorry

/-- The degreewise map from the Beilinson matrix algebra to the endomorphism DGA of its
degree-zero complex. -/
noncomputable def endomorphismDGAHom :
    CochainDGAlgebra.ofAlgebra ℤ (matrixAlgebra A n) ⟶
      endDGA.{u, u} (complex A n) where
  map i := if h : i = 0 then
    { toFun := fun x ↦
        let r := (CochainDGAlgebra.ofAlgebraZeroIso ℤ
          (matrixAlgebra A n)).hom
            (eqToHom
              (congrArg (fun j : ℤ ↦
                (CochainDGAlgebra.ofAlgebra ℤ (matrixAlgebra A n)).X j) h) x)
        let f := (CochainComplex.singleFunctor (scheme A n).Modules 0).map
          (toEnd A n r)
        eqToHom (congrArg (fun j : ℤ ↦
          (endDGA.{u, u} (complex A n)).X j) h.symm)
          (Cocycle.equivHom (complex A n) (complex A n) f).1
      map_add' := sorry
      map_smul' := sorry }
    else 0
  comm_d := sorry
  map_one := sorry
  map_mul := sorry

/-- In degree zero, `endomorphismDGAHom` is the action `toEnd` on the Beilinson generator. -/
theorem endomorphismDGAHom_apply_zero (r : matrixAlgebra A n) :
    endomorphismDGAHom A n 0
        ((CochainDGAlgebra.ofAlgebraZeroIso ℤ (matrixAlgebra A n)).inv r) =
      (Cocycle.equivHom (complex A n) (complex A n)
        ((CochainComplex.singleFunctor (scheme A n).Modules 0).map (toEnd A n r))).1 := sorry

/-- The Beilinson action identifies the matrix algebra with the derived endomorphism DGA. -/
theorem endomorphismDGAHom_quasiIso :
    CochainDGAlgebra.quasiIso (endomorphismDGAHom A n) := sorry

/-- The regular right `matrixAlgebra A n`-module in its ordinary derived category, transported
from the canonical regular module over the degree-zero DGA. -/
noncomputable def regularObject :
    DerivedCategory (ModuleCat ((matrixAlgebra A n)ᵐᵒᵖ)) :=
  (DifferentialGradedModule.DegreeZero.fromDerived ℤ (matrixAlgebra A n)).obj
    (DifferentialGradedModule.Derived.regularObject
      (CochainDGAlgebra.ofAlgebra ℤ (matrixAlgebra A n)))

/-- Derived tensoring over the Beilinson matrix algebra with the Beilinson complex. -/
noncomputable def tensorFunctor :
    DerivedCategory (ModuleCat ((matrixAlgebra A n)ᵐᵒᵖ)) ⥤
      Scheme.ModuleDerived.Quasicoherent (scheme A n) :=
  DifferentialGradedModule.DegreeZero.toDerived ℤ (matrixAlgebra A n) ⋙
    CochainDGAlgebra.Hom.Derived.extension (endomorphismDGAHom A n) ⋙
    (Scheme.ModuleDerived.quasicoherentProperty (scheme A n)).lift
      (SheafOfModules.RingedSite.TensorWithObject.Derived.tensorFunctor
        (complex A n))
      (ambientTensorFunctor_mem A n)

/-- The Beilinson tensor functor is the composite through the degree-zero DGA and the
endomorphism DGA of `complex A n`. -/
theorem tensorFunctor_def :
    tensorFunctor A n =
      DifferentialGradedModule.DegreeZero.toDerived ℤ (matrixAlgebra A n) ⋙
        CochainDGAlgebra.Hom.Derived.extension (endomorphismDGAHom A n) ⋙
        (Scheme.ModuleDerived.quasicoherentProperty (scheme A n)).lift
          (SheafOfModules.RingedSite.TensorWithObject.Derived.tensorFunctor
            (complex A n))
          (ambientTensorFunctor_mem A n) := sorry

/-- The Beilinson tensor functor is `A`-linear. -/
theorem tensorFunctor_linear : (tensorFunctor A n).Linear A := sorry

/-- The Beilinson tensor functor carries its canonical compatibility with integer shifts. -/
@[reducible]
noncomputable def tensorFunctor_commShift :
    (tensorFunctor A n).CommShift ℤ :=
  @Functor.CommShift.comp _ _ _ _ _ _
    (DifferentialGradedModule.DegreeZero.toDerived ℤ (matrixAlgebra A n) ⋙
      CochainDGAlgebra.Hom.Derived.extension (endomorphismDGAHom A n))
    ((Scheme.ModuleDerived.quasicoherentProperty (scheme A n)).lift
      (SheafOfModules.RingedSite.TensorWithObject.Derived.tensorFunctor
        (complex A n))
      (ambientTensorFunctor_mem A n)) ℤ _ _ _ _
    (Functor.CommShift.comp
      (DifferentialGradedModule.DegreeZero.toDerived ℤ (matrixAlgebra A n))
      (CochainDGAlgebra.Hom.Derived.extension (endomorphismDGAHom A n)))
    (@Functor.CommShift.ofComp _ _ _ _ _ _ _ _ _
      ((Scheme.ModuleDerived.quasicoherentProperty (scheme A n)).liftCompιIso
        (SheafOfModules.RingedSite.TensorWithObject.Derived.tensorFunctor
          (complex A n))
        (ambientTensorFunctor_mem A n)) _ _ ℤ _ _ _ _ _
      (SheafOfModules.RingedSite.TensorWithObject.Derived.tensorFunctor_commShift
        (complex A n)))

/-- The Beilinson tensor functor preserves distinguished triangles. -/
theorem tensorFunctor_isTriangulated :
    (tensorFunctor A n).IsTriangulatedWith (tensorFunctor_commShift A n) := sorry

/-- The Beilinson tensor functor is an equivalence. -/
theorem tensorFunctor_isEquivalence :
    (tensorFunctor A n).IsEquivalence := sorry

/-- The canonical transport of the ordinary regular module to the regular module over the
endomorphism DGA of the Beilinson complex. -/
noncomputable def regularTransportIso :
    (CochainDGAlgebra.Hom.Derived.extension.{0, u} (endomorphismDGAHom A n)).obj
        ((DifferentialGradedModule.DegreeZero.toDerived ℤ
          (matrixAlgebra A n)).obj (regularObject A n)) ≅
      DifferentialGradedModule.Derived.regularObject
        (endDGA.{u, u} (complex A n)) :=
  ((CochainDGAlgebra.Hom.Derived.extension.{0, u}
    (endomorphismDGAHom A n)).mapIso
      ((DifferentialGradedModule.DegreeZero.equivalence ℤ
        (matrixAlgebra A n)).counitIso.app
          (DifferentialGradedModule.Derived.regularObject
            (CochainDGAlgebra.ofAlgebra ℤ (matrixAlgebra A n))))).trans
    ((DifferentialGradedBimodule.Tensor.regularObjectIso
      (DifferentialGradedBimodule.ChangeOfRings.extension.{0, u, 0}
        (endomorphismDGAHom A n))).trans
      (((DifferentialGradedModule.Derived.Q.{0, u}
        (endDGA.{u, u} (complex A n))).mapIso
          ((DifferentialGradedModule.toK
            (endDGA.{u, u} (complex A n))).mapIso
              (eqToIso
                (DifferentialGradedBimodule.ChangeOfRings.extension_toRightModule
                  (endomorphismDGAHom A n))))).trans
        ((DifferentialGradedModule.Derived.Q.{0, u}
          (endDGA.{u, u} (complex A n))).mapIso
            (DifferentialGradedModule.Derived.regularZeroIso
              (endDGA.{u, u} (complex A n)))).symm))

/-- The ambient derived-category comparison underlying the image of the regular object. -/
noncomputable def regularDerivedIso :
    ((tensorFunctor A n).obj (regularObject A n)).obj ≅
      (derivedBeilinsonGenerator A n).obj :=
  (SheafOfModules.RingedSite.TensorWithObject.Derived.tensorFunctor
      (complex A n)).mapIso (regularTransportIso A n) ≪≫
    SheafOfModules.RingedSite.TensorWithObject.Derived.regularComparisonIso
      (complex A n) ≪≫
      (eqToIso (derivedBeilinsonGenerator_obj A n)).symm

/-- The Beilinson tensor functor sends the regular matrix-algebra object to the Beilinson
generator in the derived category of modules with quasicoherent cohomology. -/
noncomputable def regularIso :
    (tensorFunctor A n).obj (regularObject A n) ≅ derivedBeilinsonGenerator A n :=
  ObjectProperty.isoMk _ (regularDerivedIso A n)

/-- The forward morphism of `regularIso` is the canonical regular-object comparison. -/
theorem regularIso_hom :
    (regularIso A n).hom = ObjectProperty.homMk (regularDerivedIso A n).hom := sorry

end AlgebraicGeometry.ProjectiveSpace.Beilinson

end
