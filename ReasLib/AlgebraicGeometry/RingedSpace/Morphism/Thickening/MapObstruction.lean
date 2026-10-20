/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Extension.Obstruction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Thickening.Flat
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Lift

/-!
# Relative obstruction to lifting module maps

For a strict morphism of first-order thickenings, modules flat over the thickened
base have canonical source-ideal extensions. The Baer difference for the endpoint
maps `φ` and `1 ⊗ φ` defines an Ext-one class which vanishes exactly when `φ` lifts.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace (Modules)
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Hom.ModuleExtension
open AlgebraicGeometry.RingedSpace.Hom.ModuleMap (Lift)
open CategoryTheory.Abelian (Ext)
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Thickening.Hom

variable {T U : Thickening.{u}} [IsFirstOrderThickening T.hom] [IsFirstOrderThickening U.hom]
variable (g : T ⟶ U)

private theorem ofSourceIdealMul_zero (F' : T.right.Modules) :
    ((T.hom _*).map (sourceIdealMulMap g F') ≫ (ofPullback T.hom F').ι) ≫
      (ofPullback T.hom F').π = 0 := sorry

private theorem ofSourceIdealMul_shortExact (F' : T.right.Modules)
    [SheafOfModules.IsFlatOver F' g.right] (hg : IsStrict g) :
    (ShortComplex.mk
      ((T.hom _*).map (sourceIdealMulMap g F') ≫ (ofPullback T.hom F').ι)
      (ofPullback T.hom F').π (ofSourceIdealMul_zero g F')).ShortExact := sorry

/-- The mixed-scalar extension `0 ⟶ f^* 𝒥 ⊗ i^* ℱ' ⟶ ℱ' ⟶ i_* i^* ℱ' ⟶ 0`
whose inclusion is the source-ideal action followed by the reduction-kernel inclusion,
for a module flat over the thickened base and a strict morphism of thickenings. -/
def ofSourceIdealMul (F' : T.right.Modules)
    [SheafOfModules.IsFlatOver F' g.right] (hg : IsStrict g) : ModuleExtension T.hom :=
  ModuleExtension.mk
    ((g.left ^*).obj (idealModule U.hom) ⊗ (T.hom^*).obj F') ((T.hom^*).obj F') F'
    ((T.hom _*).map (sourceIdealMulMap g F') ≫ (ofPullback T.hom F').ι)
    (ofPullback T.hom F').π (by exact ofSourceIdealMul_zero g F')
    (by exact ofSourceIdealMul_shortExact g F' hg)

/-- The source-ideal extension has its specified kernel, middle, quotient, inclusion,
and reduction projection. -/
theorem ofSourceIdealMul_spec (F' : T.right.Modules)
    [SheafOfModules.IsFlatOver F' g.right] (hg : IsStrict g) :
    (ofSourceIdealMul g F' hg).kernel =
        (g.left ^*).obj (idealModule U.hom) ⊗ (T.hom^*).obj F' ∧
      (ofSourceIdealMul g F' hg).middle = F' ∧
      (ofSourceIdealMul g F' hg).cokernel = (T.hom^*).obj F' ∧
      (ofSourceIdealMul g F' hg).ι =
        (T.hom _*).map (sourceIdealMulMap g F') ≫ (ofPullback T.hom F').ι ∧
      (ofSourceIdealMul g F' hg).π = (ofPullback T.hom F').π :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The infinitesimal-map square of `φ` and `1 ⊗ φ` commutes for the source-ideal
extensions of modules flat over the thickened base of a strict morphism. -/
theorem sourceIdealMul_infinitesimalMap_comm {F' G' : T.right.Modules}
    [SheafOfModules.IsFlatOver F' g.right] [SheafOfModules.IsFlatOver G' g.right]
    (hg : IsStrict g) (φ : (T.hom^*).obj F' ⟶ (T.hom^*).obj G') :
    infinitesimalMap_comm (ofSourceIdealMul g F' hg) (ofSourceIdealMul g G' hg) φ
      (tensorHom (𝟙 ((g.left ^*).obj (idealModule U.hom))) φ) := sorry

variable [HasExt.{u} T.left.Modules]

/-- The Ext-one obstruction to lifting a map between reductions of modules flat over
the thickened base of a strict morphism of first-order thickenings, given by the
Baer difference with endpoint maps `φ` and `1 ⊗ φ`. -/
def obstruction {F' G' : T.right.Modules}
    [SheafOfModules.IsFlatOver F' g.right] [SheafOfModules.IsFlatOver G' g.right]
    (hg : IsStrict g) (φ : (T.hom^*).obj F' ⟶ (T.hom^*).obj G') :
    Ext ((T.hom^*).obj F')
      ((g.left ^*).obj (idealModule U.hom) ⊗ (T.hom^*).obj G') 1 :=
  mapObstruction (ofSourceIdealMul g F' hg) (ofSourceIdealMul g G' hg) φ
    (tensorHom (𝟙 ((g.left ^*).obj (idealModule U.hom))) φ)
    (sourceIdealMul_infinitesimalMap_comm g hg φ)

/-- The relative map obstruction is the endpoint-map obstruction of the two
source-ideal extensions with kernel map `1 ⊗ φ`. -/
theorem obstruction_eq {F' G' : T.right.Modules}
    [SheafOfModules.IsFlatOver F' g.right] [SheafOfModules.IsFlatOver G' g.right]
    (hg : IsStrict g) (φ : (T.hom^*).obj F' ⟶ (T.hom^*).obj G') :
    obstruction g hg φ =
      mapObstruction (ofSourceIdealMul g F' hg) (ofSourceIdealMul g G' hg) φ
        (tensorHom (𝟙 ((g.left ^*).obj (idealModule U.hom))) φ)
        (sourceIdealMul_infinitesimalMap_comm g hg φ) := rfl

/-- Along a strict morphism of first-order thickenings, a map between reductions of
modules flat over the thickened base lifts if and only if its relative Ext-one
obstruction vanishes. -/
theorem obstruction_eq_zero_iff {F' G' : T.right.Modules}
    [SheafOfModules.IsFlatOver F' g.right] [SheafOfModules.IsFlatOver G' g.right]
    (hg : IsStrict g) (φ : (T.hom^*).obj F' ⟶ (T.hom^*).obj G') :
    obstruction g hg φ = 0 ↔ Nonempty (Lift F' G' φ) := sorry

end AlgebraicGeometry.RingedSpace.Thickening.Hom
