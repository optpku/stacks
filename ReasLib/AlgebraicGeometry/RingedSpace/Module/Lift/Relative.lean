module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Lift
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Thickening.Flat
public import Mathlib.CategoryTheory.HomCongr

/-!
# Relative translations of lifts of module maps

The source-ideal tensor comparison induces translations of lifts of reduced module maps.
For a strict morphism of first-order thickenings and a target module flat over the
thickened base, each pair of lifts is connected by exactly one relative translation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace (Modules)
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Hom.ModuleMap
open AlgebraicGeometry.RingedSpace.Hom.ModuleMap.Lift
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Thickening.Hom
namespace ModuleMap

variable {T U : Thickening.{u}}
variable [hT : IsFirstOrderThickening T.hom] [hU : IsFirstOrderThickening U.hom]
include hT hU
variable (g : T ⟶ U)

/-- The comparison `𝒢 ⊗ f^* 𝒥 ⟶ ℐ𝒢'` obtained by braiding the canonical map
`f^* 𝒥 ⊗ 𝒢 ⟶ ℐ𝒢'`. -/
def sourceIdealTensorCompare (G' : T.right.Modules) :
    (T.hom^*).obj G' ⊗ (g.left^*).obj (idealModule U.hom) ⟶
      idealMulRestrict T.hom G' :=
  (β_ ((T.hom^*).obj G') ((g.left^*).obj (idealModule U.hom))).hom ≫
    sourceIdealMulMap g G'

/-- The tensor comparison is the braiding followed by the source-ideal action. -/
theorem sourceIdealTensorCompare_comp (G' : T.right.Modules) :
    sourceIdealTensorCompare g G' =
      (β_ ((T.hom^*).obj G') ((g.left^*).obj (idealModule U.hom))).hom ≫
        sourceIdealMulMap g G' := sorry

variable {F' G' : T.right.Modules}
variable {φ : (T.hom^*).obj F' ⟶ (T.hom^*).obj G'}

/-- Translate a lift of a reduced module map by a map into the relative ideal tensor. -/
def relativePerturb {T U : Thickening.{u}}
    [hT : IsFirstOrderThickening T.hom] [hU : IsFirstOrderThickening U.hom]
    (g : T ⟶ U) {F' G' : T.right.Modules}
    {φ : (T.hom^*).obj F' ⟶ (T.hom^*).obj G'}
    (α : (T.hom^*).obj F' ⟶
      (T.hom^*).obj G' ⊗ (g.left^*).obj (idealModule U.hom))
    (φ' : Lift F' G' φ) : Lift F' G' φ :=
  perturb (i := T.hom) (α ≫ sourceIdealTensorCompare g G') φ'

/-- The underlying map of a relative translate is the ideal-valued perturbation
obtained by postcomposition with the tensor comparison. -/
theorem relativePerturb_hom
    (α : (T.hom^*).obj F' ⟶
      (T.hom^*).obj G' ⊗ (g.left^*).obj (idealModule U.hom))
    (φ' : Lift F' G' φ) :
    (relativePerturb g α φ').hom =
      (perturb (α ≫ sourceIdealTensorCompare g G') φ').hom := sorry

/-- Relative translation by zero leaves a lift unchanged. -/
theorem relativePerturb_zero (φ' : Lift F' G' φ) :
    relativePerturb g 0 φ' = φ' := sorry

/-- Relative translation by a sum is successive translation by its summands. -/
theorem relativePerturb_add
    (α β : (T.hom^*).obj F' ⟶
      (T.hom^*).obj G' ⊗ (g.left^*).obj (idealModule U.hom))
    (φ' : Lift F' G' φ) :
    relativePerturb g (α + β) φ' = relativePerturb g α (relativePerturb g β φ') := sorry

/-- When the source-ideal action is invertible, postcomposition with the tensor
comparison identifies relative tensor-valued maps with ideal-valued maps. -/
def homSourceIdealMulEquiv {T U : Thickening.{u}}
    [hT : IsFirstOrderThickening T.hom] [hU : IsFirstOrderThickening U.hom]
    (g : T ⟶ U) {G' : T.right.Modules} [hIso : IsIso (sourceIdealMulMap g G')]
    (F' : T.right.Modules) :
    ((T.hom^*).obj F' ⟶
      (T.hom^*).obj G' ⊗ (g.left^*).obj (idealModule U.hom)) ≃
      ((T.hom^*).obj F' ⟶ idealMulRestrict T.hom G') :=
  ((Iso.refl ((T.hom^*).obj F')).homCongr
      (β_ ((T.hom^*).obj G') ((g.left^*).obj (idealModule U.hom)))).trans
    ((Iso.refl ((T.hom^*).obj F')).homCongr
      (@asIso _ _ _ _ (sourceIdealMulMap g G') hIso))

/-- The forward Hom-set comparison is postcomposition with the tensor comparison. -/
theorem homSourceIdealMulEquiv_apply [IsIso (sourceIdealMulMap g G')]
    {F' : T.right.Modules}
    (α : (T.hom^*).obj F' ⟶
      (T.hom^*).obj G' ⊗ (g.left^*).obj (idealModule U.hom)) :
    homSourceIdealMulEquiv g F' α = α ≫ sourceIdealTensorCompare g G' := sorry

/-- When the source-ideal action is invertible, relative translation from a supplied
lift parametrizes all lifts of the same reduced module map. -/
def relativePerturbEquiv {T U : Thickening.{u}}
    [hT : IsFirstOrderThickening T.hom] [hU : IsFirstOrderThickening U.hom]
    (g : T ⟶ U) {F' G' : T.right.Modules}
    {φ : (T.hom^*).obj F' ⟶ (T.hom^*).obj G'}
    [hIso : IsIso (sourceIdealMulMap g G')] (φ' : Lift F' G' φ) :
    ((T.hom^*).obj F' ⟶
      (T.hom^*).obj G' ⊗ (g.left^*).obj (idealModule U.hom)) ≃
      Lift F' G' φ :=
  (homSourceIdealMulEquiv g F').trans (perturbEquiv φ')

/-- The forward lift parametrization is the concrete relative translation. -/
theorem relativePerturbEquiv_apply [IsIso (sourceIdealMulMap g G')]
    (φ' : Lift F' G' φ)
    (α : (T.hom^*).obj F' ⟶
      (T.hom^*).obj G' ⊗ (g.left^*).obj (idealModule U.hom)) :
    relativePerturbEquiv g φ' α = relativePerturb g α φ' := sorry

/-- Along a strict morphism of first-order thickenings, every pair of lifts into a
module flat over the thickened base is related by exactly one relative translation. -/
theorem lift_principalHomogeneous [SheafOfModules.IsFlatOver G' g.right]
    (hg : IsStrict g) (φ' φ'' : Lift F' G' φ) :
    ∃! α : (T.hom^*).obj F' ⟶
        (T.hom^*).obj G' ⊗ (g.left^*).obj (idealModule U.hom),
      relativePerturb g α φ' = φ'' := sorry

end ModuleMap
end AlgebraicGeometry.RingedSpace.Thickening.Hom
