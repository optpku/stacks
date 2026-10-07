module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import stacks_project.Chap91.Lemma_91_4_2_Obstruction
public import stacks_project.Chap91.Lemma_91_5_1_IdealMul
public import stacks_project.Chap91.Lemma_91_5_2_Comparison
public import stacks_project.Chap91.Situation_91_6_2_Diagram

/-!
# Relative Ext¹ obstruction of a map of modules along a strict morphism of first-order thickenings

A strict morphism of first-order thickenings and an `𝒪_X`-linear map `φ : i^* ℱ' ⟶ i^* 𝒢'`
between modules flat over `S'` determine a mixed-scalar extension with kernel
`f^* 𝒥 ⊗ i^* ℱ'` and a canonical class `o(φ)` in `Ext (i^* ℱ') (f^* 𝒥 ⊗ i^* 𝒢') 1`,
obtained from the 91.4.2 difference of endpoint maps with `ψ = 1 ⊗ φ`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace (Modules)
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Hom.ModuleExtension
open CategoryTheory.Abelian (Ext)
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Thickening
namespace Hom

variable {T U : Thickening.{u}} [IsFirstOrderThickening T.hom] [IsFirstOrderThickening U.hom]
variable (g : T ⟶ U)

/-- The mixed-scalar extension `0 ⟶ f^* 𝒥 ⊗ i^* ℱ' ⟶ ℱ' ⟶ i_* i^* ℱ' ⟶ 0` obtained by
reassociating `ofPullback` along `sourceIdealMulMap`, for `ℱ'` flat over `S'` and `g` strict. -/
def ofSourceIdealMul (F' : T.right.Modules)
    [SheafOfModules.IsFlatOver F' g.right] (hg : IsStrict g) : ModuleExtension T.hom :=
  mk ((g.left ^*).obj (idealModule U.hom) ⊗ (T.hom^*).obj F') ((T.hom^*).obj F') F'
    ((T.hom _*).map (sourceIdealMulMap g F') ≫ (ofPullback T.hom F').ι)
    (ofPullback T.hom F').π sorry sorry

/-- The kernel, middle, cokernel, inclusion, and projection of `ofSourceIdealMul`. -/
theorem ofSourceIdealMul_spec (F' : T.right.Modules)
    [SheafOfModules.IsFlatOver F' g.right] (hg : IsStrict g) :
    (ofSourceIdealMul g F' hg).kernel =
        (g.left ^*).obj (idealModule U.hom) ⊗ (T.hom^*).obj F' ∧
      (ofSourceIdealMul g F' hg).middle = F' ∧
      (ofSourceIdealMul g F' hg).cokernel = (T.hom^*).obj F' ∧
      (ofSourceIdealMul g F' hg).ι =
        (T.hom _*).map (sourceIdealMulMap g F') ≫ (ofPullback T.hom F').ι ∧
      (ofSourceIdealMul g F' hg).π = (ofPullback T.hom F').π := sorry

/-- The kernel map `ψ = 1 ⊗ φ` associated to an `𝒪_X`-linear map `φ : i^* ℱ' ⟶ i^* 𝒢'`. -/
def tensorKernelMap {F' G' : T.right.Modules}
    (φ : (T.hom^*).obj F' ⟶ (T.hom^*).obj G') :
    (g.left ^*).obj (idealModule U.hom) ⊗ (T.hom^*).obj F' ⟶
      (g.left ^*).obj (idealModule U.hom) ⊗ (T.hom^*).obj G' :=
  tensorHom (𝟙 ((g.left ^*).obj (idealModule U.hom))) φ

/-- `tensorKernelMap g φ` is `tensorHom (𝟙 (f^* 𝒥)) φ`. -/
theorem tensorKernelMap_eq {F' G' : T.right.Modules}
    (φ : (T.hom^*).obj F' ⟶ (T.hom^*).obj G') :
    tensorKernelMap g φ = tensorHom (𝟙 ((g.left ^*).obj (idealModule U.hom))) φ := sorry

/-- The infinitesimal-map square of `φ` and `1 ⊗ φ` commutes for `ofSourceIdealMul`. -/
theorem tensorKernelMap_comm {F' G' : T.right.Modules}
    [SheafOfModules.IsFlatOver F' g.right] [SheafOfModules.IsFlatOver G' g.right]
    (hg : IsStrict g) (φ : (T.hom^*).obj F' ⟶ (T.hom^*).obj G') :
    infinitesimalMap_comm (ofSourceIdealMul g F' hg) (ofSourceIdealMul g G' hg) φ
      (tensorKernelMap g φ) := sorry

/-- The descended `𝒪_X`-module extension `0 ⟶ f^* 𝒥 ⊗ i^* 𝒢' ⟶ ℋ ⟶ i^* ℱ' ⟶ 0`
representing `o(φ)`. -/
def obstructionExtension {F' G' : T.right.Modules}
    [SheafOfModules.IsFlatOver F' g.right] [SheafOfModules.IsFlatOver G' g.right]
    (hg : IsStrict g) (φ : (T.hom^*).obj F' ⟶ (T.hom^*).obj G') :
    CategoryTheory.Extension
      ((g.left ^*).obj (idealModule U.hom) ⊗ (T.hom^*).obj G') ((T.hom^*).obj F') :=
  let δ :=
    differenceExtension (ofSourceIdealMul g F' hg) (ofSourceIdealMul g G' hg) φ
      (tensorKernelMap g φ)
  let i := T.hom
  let L := (g.left ^*).obj (idealModule U.hom) ⊗ (T.hom^*).obj G'
  let F := (T.hom^*).obj F'
  { E := (i ^*).obj δ.E
    f := (asIso ((pullbackPushforwardAdjunction i).counit.app L)).inv ≫ (i ^*).map δ.f
    g := (i ^*).map δ.g ≫ (asIso ((pullbackPushforwardAdjunction i).counit.app F)).hom
    zero := sorry
    shortExact := sorry }

variable [HasExt.{u} T.left.Modules]

/-- The obstruction class `o(φ) ∈ Ext¹_{𝒪_X}(i^* ℱ', f^* 𝒥 ⊗ i^* 𝒢')` of an `𝒪_X`-linear
map along a strict morphism of first-order thickenings, for modules flat over `S'`. -/
def obstruction {F' G' : T.right.Modules}
    [SheafOfModules.IsFlatOver F' g.right] [SheafOfModules.IsFlatOver G' g.right]
    (hg : IsStrict g) (φ : (T.hom^*).obj F' ⟶ (T.hom^*).obj G') :
    Ext ((T.hom^*).obj F')
      ((g.left ^*).obj (idealModule U.hom) ⊗ (T.hom^*).obj G') 1 :=
  (obstructionExtension g hg φ).extClass

/-- `obstruction g hg φ` is the 91.4.2 class `o(φ, 1 ⊗ φ)` of `ofSourceIdealMul`. -/
theorem obstruction_eq {F' G' : T.right.Modules}
    [SheafOfModules.IsFlatOver F' g.right] [SheafOfModules.IsFlatOver G' g.right]
    (hg : IsStrict g) (φ : (T.hom^*).obj F' ⟶ (T.hom^*).obj G') :
    obstruction g hg φ =
      mapObstruction (ofSourceIdealMul g F' hg) (ofSourceIdealMul g G' hg) φ
        (tensorKernelMap g φ) (tensorKernelMap_comm g hg φ) := sorry

end Hom
end AlgebraicGeometry.RingedSpace.Thickening
