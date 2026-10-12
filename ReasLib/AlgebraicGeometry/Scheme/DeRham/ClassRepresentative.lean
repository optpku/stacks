/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.CanonicalAction
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.LogarithmicForms
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Underlying
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Derived
public import ReasLib.Topology.Sheaf.GlobalSections.ConstantInteger
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSiteTensorUnit
public import ReasLib.Algebra.Homology.Embedding.Functor
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory ComplexShape
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham.ClassRepresentative

-- Local instance justification (defeq pin): the coefficient localization is the same canonical module-sheaf presentation used by CanonicalAction.unitObject and DerivedPushforward.derivedComplex.
attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasDerivedCategory

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Forgetting coefficients induces an exact functor to the standard derived category of
additive sheaves on the same space. -/
noncomputable abbrev additiveForget :
    RingedSite.Hom.ModuleDerived.{u} (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom) ⥤
      DerivedCategory (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  (RingedSite.Hom.underlyingAbelianSheafFunctor.{u}
    (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom)).mapDerivedCategory

/-- The constant integer sheaf placed in degree zero in the additive derived category. -/
noncomputable abbrev integerObject (X : Scheme.{u}) :=
  (DerivedCategory.singleFunctor
    (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) 0).obj
      (TopCat.Sheaf.constantIntegerSheaf X)

/-- The localization of the actual additive relative de Rham complex extended by zero. -/
noncomputable abbrev additiveObject :
    DerivedCategory (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  DerivedCategory.Q.obj ((LogarithmicForms.additiveComplex f).extend embeddingUpNat)

/-- Exact forgetting commutes with the localization and extension of the de Rham complex. -/
noncomputable def additiveComplexIso :
    (additiveForget f).obj (DerivedPushforward.derivedComplex f) ≅ additiveObject f :=
  let M := RingedSpace.DeRham.Modules f.toLRSHom.toShHom
  let F := RingedSite.Hom.underlyingAbelianSheafFunctor.{u}
    (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom)
  let N := RingedSpace.DeRham.complex f.toLRSHom.toShHom
  let K := N.extend embeddingUpNat
  (additiveForget f).mapIso ((DerivedCategory.quotientCompQhIso M).app K) ≪≫
    F.mapDerivedCategoryFactors.app K ≪≫
      DerivedCategory.Q.mapIso (embeddingUpNat.mapAppIso F N)

/-- The forgotten coefficient unit is the additive derived single of its underlying sheaf. -/
noncomputable def coefficientUnitIso :
    (additiveForget f).obj (CanonicalAction.unitObject f) ≅
      (DerivedCategory.singleFunctor
        (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) 0).obj
          ((RingedSite.Hom.underlyingAbelianSheafFunctor.{u}
            (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom)).obj
              (𝟙_ (RingedSpace.DeRham.Modules f.toLRSHom.toShHom))) :=
  let M := RingedSpace.DeRham.Modules f.toLRSHom.toShHom
  let F := RingedSite.Hom.underlyingAbelianSheafFunctor.{u}
    (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom)
  (additiveForget f).mapIso
    ((DerivedCategory.quotientCompQhIso M).app (CanonicalAction.unitComplex f) ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ M 0).app (𝟙_ M)).symm) ≪≫
    (F.mapDerivedCategorySingleFunctor 0).app (𝟙_ M)

/-- The integer unit sends the constant integer one to the coefficient section one. -/
noncomputable def integerUnit :
    integerObject X ⟶ (additiveForget f).obj (CanonicalAction.unitObject f) :=
  let J := Opens.grothendieckTopology X
  let O := RingedSpace.DeRham.coefficients f.toLRSHom.toShHom
  let F := RingedSite.Hom.underlyingAbelianSheafFunctor.{u}
    (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom)
  let oneMap := (TopCat.Sheaf.constantIntegerHomEquivTopSection X
    (F.obj (SheafOfModules.RingedSite.unitModule J O))).symm
      (1 : O.obj.obj (Opposite.op (⊤ : X.Opens)))
  (DerivedCategory.singleFunctor (Sheaf J AddCommGrpCat.{u}) 0).map
    (oneMap ≫ F.map (SheafOfModules.RingedSite.unitIsoTensorUnit (J := J) (𝒪 := O)).hom) ≫
      (coefficientUnitIso f).inv

/-- A de Rham class gives its shifted additive representative by evaluation on the unit. -/
noncomputable def map (n : ℤ) (ξ : cohomology f n) :
    ShiftedHom (integerObject X) (additiveObject f) n :=
  integerUnit f ≫ (additiveForget f).map (CanonicalAction.unitClass f n ξ) ≫
    ((additiveForget f).commShiftIso n).hom.app (DerivedPushforward.derivedComplex f) ≫
      (additiveComplexIso f).hom⟦n⟧'

/-- Evaluation on the integer unit identifies de Rham cohomology with additive representatives. -/
theorem map_bijective (n : ℤ) : Function.Bijective (map f n) := sorry

/-- Recover a de Rham class using the inverse function of the fixed realization map. -/
noncomputable def inverse (n : ℤ) :
    ShiftedHom (integerObject X) (additiveObject f) n → cohomology f n :=
  Function.invFun (map f n)

/-- Every additive representative is realized by its recovered de Rham class. -/
theorem map_inverse (n : ℤ) (φ : ShiftedHom (integerObject X) (additiveObject f) n) :
    map f n (inverse f n φ) = φ := sorry

/-- Recovering the representative of a de Rham class returns that class. -/
theorem inverse_map (n : ℤ) (ξ : cohomology f n) :
    inverse f n (map f n ξ) = ξ := sorry

end AlgebraicGeometry.Scheme.DeRham.ClassRepresentative
