/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InternalHom
public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Model
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.RHom.IdealQuotient
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Tensor
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Kunneth.SingleSheaf
public import ReasLib.CategoryTheory.DerivedCategory.Ext.TStructure
public import ReasLib.CategoryTheory.Monoidal.Closed.Triangulated
public import ReasLib.CategoryTheory.Shift.ShiftedHom.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Basic

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open RingedSpace
open SheafOfModules.RingedSite.InternalHom
open DerivedCategory MonoidalClosed ModuleDerived
open DerivedCategory.ShiftedHom.Boundary
open AlgebraicGeometry.Scheme.Modules.Kunneth.SingleSheaf
open scoped MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.IdealSubobject

/-- The canonical morphism from the conormal internal Hom to degree-one derived
self-Ext, obtained from the boundary of the second-order thickening row and
tensor evaluation. -/
noncomputable def conormalExtOneComparison
    {Y : RingedSpace.{u}} [KFlat.HomotopyTensorDescends Y]
    [KFlat.TensorDescends Y] [KFlat.IsLocalization Y]
    (H : MonoidalClosed (ModuleDerived Y)) (I : IdealSubobject Y)
    [((tensoringRight (ModuleDerived Y)).obj
      ((singleFunctor Y.Modules 0).obj
        (obj Y.sheaf (conormalModule I) (quotientStructureModule I)))).CommShift ℤ]
    [(ihomOf H ((singleFunctor Y.Modules 0).obj
      (quotientStructureModule I))).CommShift ℤ] :
    obj Y.sheaf (conormalModule I) (quotientStructureModule I) ⟶
      quotientSelfExt H I 1 :=
  let K := conormalModule I
  let Q := quotientStructureModule I
  let N := obj Y.sheaf K Q
  let K' := (singleFunctor Y.Modules 0).obj K
  let Q' := (singleFunctor Y.Modules 0).obj Q
  let N' := (singleFunctor Y.Modules 0).obj N
  let delta : CategoryTheory.ShiftedHom Q' K' (1 : ℤ) :=
    (secondOrderThickeningRow_shortExact I).singleδ
  let evaluation : K ⊗ N ⟶ Q :=
    (homEquiv Y.sheaf K N Q).symm (𝟙 N)
  let derivedEvaluation : K' ⊗ N' ⟶ Q' :=
    @tensorComparison Y _ _ _ (ModuleDerived.modulesHasKFlatResolutions Y)
        _ _ _ _ K N ≫
      (singleFunctor Y.Modules 0).map evaluation
  let shiftedEvaluation : CategoryTheory.ShiftedHom (Q' ⊗ N') Q' (1 : ℤ) :=
    ((tensoringRight (ModuleDerived Y)).obj N').map delta ≫
      (((tensoringRight (ModuleDerived Y)).obj N').commShiftIso (1 : ℤ)).hom.app K' ≫
        (shiftFunctor (ModuleDerived Y) (1 : ℤ)).map derivedEvaluation
  ((singleFunctorCompHomologyFunctorIso Y.Modules 0).inv.app N) ≫
    toHomology N' ((ihomOf H Q').obj Q') 0 1
      (((adjunctionOf H Q').shiftedHomEquiv N' Q' (1 : ℤ)).symm shiftedEvaluation)

/-- For an ideal sheaf `I ⊆ 𝒪_Y`, the canonical comparison
`Hom_𝒪_Y(I / I ^ 2, 𝒪_Y / I) ⟶ Ext^1_𝒪_Y(𝒪_Y / I, 𝒪_Y / I)` is an
isomorphism. -/
@[stacks 0BQW]
noncomputable instance conormalExtOneComparison_isIso
    {Y : RingedSpace.{u}} [KFlat.HomotopyTensorDescends Y]
    [KFlat.TensorDescends Y] [KFlat.IsLocalization Y]
    (H : MonoidalClosed (ModuleDerived Y)) (I : IdealSubobject Y)
    [((tensoringRight (ModuleDerived Y)).obj
      ((singleFunctor Y.Modules 0).obj
        (obj Y.sheaf (conormalModule I) (quotientStructureModule I)))).CommShift ℤ]
    [(ihomOf H ((singleFunctor Y.Modules 0).obj
      (quotientStructureModule I))).CommShift ℤ] :
    IsIso (conormalExtOneComparison H I) := sorry

end AlgebraicGeometry.RingedSpace.IdealSubobject
