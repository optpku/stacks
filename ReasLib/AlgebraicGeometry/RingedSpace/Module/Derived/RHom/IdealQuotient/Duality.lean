/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Rank
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InternalHom
public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Model
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.AlgebraSheaf.ExteriorPower
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.RHom.IdealQuotient
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Tensor
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Derived
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Regularity.Conormal

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry
open RingedSpace
open SheafOfModules.RingedSite.InternalHom
open DerivedCategory MonoidalClosed ModuleDerived

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.IdealSubobject

/-- The dual conormal module `Hom_𝒪_Y(I / I², 𝒪_Y / I)` of an ideal subobject. -/
noncomputable def conormalDual {Y : RingedSpace.{u}} (I : IdealSubobject Y) : Y.Modules :=
  obj Y.sheaf (conormalModule I) (quotientStructureModule I)

/-- The positive natural-valued rank of the conormal module at a point. -/
noncomputable def generatorRank {Y : RingedSpace.{u}} (I : IdealSubobject Y) (y : Y) : ℕ :=
  max 1 (SheafOfModules.rankAtStalk (idealConormalModule I) y).toNat

/-- The generator rank of an ideal subobject is positive at every point. -/
theorem generatorRank_pos {Y : RingedSpace.{u}} (I : IdealSubobject Y) (y : Y) :
    0 < generatorRank I y := sorry

/-- A finite Koszul-regular generating family computes the conormal generator rank at a support
point. -/
theorem generatorRank_eq_of_koszulRegularGenerators
    {Y : RingedSpace.{u}} (I : IdealSubobject Y) (U : Opens Y) (y : Y) (hy : y ∈ U)
    (hy_support : y ∈ idealQuotientSupport I)
    (n : ℕ) (f : Fin n → (I : Y.Modules).val.obj (op U))
    (h_regular : SectionSequence.IsKoszulRegular
      (fun j ↦ idealSectionToRingSection I U (f j)))
    (h_generates : IsGeneratedByIdealSectionFamilyOn I U f) :
    generatorRank I y = max 1 n := sorry

/-- The selected derived internal Hom `RHom_𝒪_Y(𝒪_Y / I, 𝒪_Y)`. -/
noncomputable def derivedDual
    {Y : RingedSpace.{u}} [KFlat.HomotopyTensorDescends Y]
    [KFlat.TensorDescends Y] [KFlat.IsLocalization Y]
    (H : MonoidalClosed (ModuleDerived Y)) (I : IdealSubobject Y) : ModuleDerived Y :=
  (ihomOf H ((singleFunctor Y.Modules 0).obj (quotientStructureModule I))).obj
    ((singleFunctor Y.Modules 0).obj (SheafOfModules.unit Y.ringCatSheaf))

/-- Under Koszul regularity, the derived quotient dual restricts locally to the exterior power of
the dual conormal module in the degree given by the local generator rank, shifted negatively. -/
theorem derivedDual_localIso
    {Y : RingedSpace.{u}} [KFlat.HomotopyTensorDescends Y]
    [KFlat.TensorDescends Y] [KFlat.IsLocalization Y]
    (H : MonoidalClosed (ModuleDerived Y)) (I : IdealSubobject Y)
    [IsKoszulRegularIdealSheaf I] :
    ∀ y : Y, ∃ U : Opens Y, y ∈ U ∧
      let restrict := moduleRestrictionToOpenDerived Y U
      IsIsomorphic
        (restrict.obj (derivedDual H I))
        (restrict.obj
          (((singleFunctor Y.Modules 0).obj
            (ExteriorPower.sheaf (conormalDual I) (generatorRank I y)))
              ⟦(-(generatorRank I y : ℤ))⟧)) := sorry

/-- If the conormal generator rank is constantly `r`, the derived quotient dual has the global
exterior-power description in degree `r`, shifted by `-r`. -/
theorem derivedDual_iso_of_constantRank
    {Y : RingedSpace.{u}} [KFlat.HomotopyTensorDescends Y]
    [KFlat.TensorDescends Y] [KFlat.IsLocalization Y]
    (H : MonoidalClosed (ModuleDerived Y)) (I : IdealSubobject Y)
    [IsKoszulRegularIdealSheaf I] (r : ℕ)
    (h_rank : ∀ y : Y, generatorRank I y = r) :
    IsIsomorphic (derivedDual H I)
      (((singleFunctor Y.Modules 0).obj (ExteriorPower.sheaf (conormalDual I) r))
        ⟦(-(r : ℤ))⟧) := sorry

end AlgebraicGeometry.RingedSpace.IdealSubobject
