module

public import stacks_project.Chap91.Lemma_91_5_1_Lift
public import stacks_project.Chap91.Lemma_91_5_2_Comparison
public import stacks_project.Chap91.Situation_91_6_2_Diagram

/-!
# Relative Hom-action on lifts of module maps

Along a strict morphism of first-order thickenings, if `𝒢'` is flat over `S'`,
`Hom_{𝒪_X}(ℱ, 𝒢 ⊗_{𝒪_X} f^* 𝒥)` acts on `𝒪_{X'}`-linear lifts of `φ : ℱ ⟶ 𝒢` by
postcomposition with the comparison `𝒢 ⊗ f^* 𝒥 ⟶ ℐ𝒢'`.
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

/-- The comparison `𝒢 ⊗_{𝒪_X} f^* 𝒥 ⟶ ℐ𝒢'` obtained by braiding the canonical map
`f^* 𝒥 ⊗ 𝒢 ⟶ ℐ𝒢'`. -/
def sourceIdealTensorCompare (G' : T.right.Modules) :
    (T.hom^*).obj G' ⊗ (g.left^*).obj (idealModule U.hom) ⟶
      idealMulRestrict T.hom G' :=
  (β_ ((T.hom^*).obj G') ((g.left^*).obj (idealModule U.hom))).hom ≫
    sourceIdealMulMap g G'

/-- `sourceIdealTensorCompare` is the braiding of `𝒢` with `f^* 𝒥` followed by
`sourceIdealMulMap`. -/
theorem sourceIdealTensorCompare_comp (G' : T.right.Modules) :
    sourceIdealTensorCompare g G' =
      (β_ ((T.hom^*).obj G') ((g.left^*).obj (idealModule U.hom))).hom ≫
        sourceIdealMulMap g G' := sorry

variable {F' G' : T.right.Modules}
variable {φ : (T.hom^*).obj F' ⟶ (T.hom^*).obj G'}

/-- Translate a lift of `φ` by an `𝒪_X`-linear map `α : ℱ ⟶ 𝒢 ⊗_{𝒪_X} f^* 𝒥`. -/
def relativePerturb
    (α : (T.hom^*).obj F' ⟶
      (T.hom^*).obj G' ⊗ (g.left^*).obj (idealModule U.hom))
    (φ' : Lift F' G' φ) : Lift F' G' φ :=
  @perturb T.left T.right T.hom F' G' φ hT (α ≫ sourceIdealTensorCompare g G') φ'

/-- The underlying middle map of a `Hom_{𝒪_X}(ℱ, 𝒢 ⊗_{𝒪_X} f^* 𝒥)`-translate is the
`perturb` of `φ'` by `α ≫ sourceIdealTensorCompare g G'`. -/
theorem relativePerturb_hom
    (α : (T.hom^*).obj F' ⟶
      (T.hom^*).obj G' ⊗ (g.left^*).obj (idealModule U.hom))
    (φ' : Lift F' G' φ) :
    (relativePerturb g α φ').hom =
      (perturb (α ≫ sourceIdealTensorCompare g G') φ').hom := sorry

/-- Along a strict morphism of first-order thickenings, if `𝒢'` is flat over `S'`, the
comparison `f^* 𝒥 ⊗ 𝒢 ⟶ ℐ𝒢'` is an isomorphism. -/
theorem isIso_sourceIdealMulMap_of_isFlatOver
    [SheafOfModules.IsFlatOver G' g.right] (hg : IsStrict g) :
    IsIso (sourceIdealMulMap g G') := sorry

/-- Postcomposition with `sourceIdealTensorCompare` identifies
`Hom_{𝒪_X}(ℱ, 𝒢 ⊗_{𝒪_X} f^* 𝒥)` with `Hom_{𝒪_X}(ℱ, ℐ𝒢')`. -/
def homSourceIdealMulEquiv [hμ : IsIso (sourceIdealMulMap g G')]
    (F' : T.right.Modules) :
    ((T.hom^*).obj F' ⟶
      (T.hom^*).obj G' ⊗ (g.left^*).obj (idealModule U.hom)) ≃
      ((T.hom^*).obj F' ⟶ idealMulRestrict T.hom G') :=
  ((Iso.refl ((T.hom^*).obj F')).homCongr
      (β_ ((T.hom^*).obj G') ((g.left^*).obj (idealModule U.hom)))).trans
    ((Iso.refl ((T.hom^*).obj F')).homCongr
      (@asIso _ _ _ _ (sourceIdealMulMap g G') hμ))

/-- The forward map of `homSourceIdealMulEquiv` is postcomposition with
`sourceIdealTensorCompare`. -/
theorem homSourceIdealMulEquiv_apply [IsIso (sourceIdealMulMap g G')]
    {F' : T.right.Modules}
    (α : (T.hom^*).obj F' ⟶
      (T.hom^*).obj G' ⊗ (g.left^*).obj (idealModule U.hom)) :
    homSourceIdealMulEquiv g F' α = α ≫ sourceIdealTensorCompare g G' := sorry

/-- Relative to one lift of `φ`, perturbation by `Hom_{𝒪_X}(ℱ, 𝒢 ⊗_{𝒪_X} f^* 𝒥)`
parametrizes all lifts. -/
def relativePerturbEquiv [IsIso (sourceIdealMulMap g G')] (φ' : Lift F' G' φ) :
    ((T.hom^*).obj F' ⟶
      (T.hom^*).obj G' ⊗ (g.left^*).obj (idealModule U.hom)) ≃
      Lift F' G' φ :=
  (homSourceIdealMulEquiv g F').trans (perturbEquiv φ')

/-- The forward map of `relativePerturbEquiv` is `relativePerturb`. -/
theorem relativePerturbEquiv_apply [IsIso (sourceIdealMulMap g G')]
    (φ' : Lift F' G' φ)
    (α : (T.hom^*).obj F' ⟶
      (T.hom^*).obj G' ⊗ (g.left^*).obj (idealModule U.hom)) :
    relativePerturbEquiv g φ' α = relativePerturb g α φ' := sorry

end ModuleMap
end AlgebraicGeometry.RingedSpace.Thickening.Hom
