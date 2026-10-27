/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Composition
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FlatLift
public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.SesFlat

/-!
# Flat lifts of `π^* F` and `h^* F'_2`

For a short exact diagram of flat first-order thickenings, the split pullback and
the pullback of the middle module are flat lifts of its restriction.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace (Modules)
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Thickening.Hom (FlatLift)
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace
namespace IsFirstOrderThickening
namespace SesFlatThickenings

variable {X S X1 X2 X3 S1 S2 S3 : RingedSpace.{u}}
variable {f : X ⟶ S} {i1 : X ⟶ X1} {i2 : X ⟶ X2} {i3 : X ⟶ X3}
variable {t1 : S ⟶ S1} {t2 : S ⟶ S2} {t3 : S ⟶ S3}
variable [IsFirstOrderThickening i1] [IsFirstOrderThickening i2]
variable [IsFirstOrderThickening i3] [IsFirstOrderThickening t1]
variable [IsFirstOrderThickening t2] [IsFirstOrderThickening t3]

/-- The restriction `F = F'_2|_X` is flat over `S`. -/
theorem moduleRestrict_isFlatOver (σ : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :
    SheafOfModules.IsFlatOver (moduleRestrict σ) f := sorry

/-- The inverse image `π^* F` is flat over `S'_1`. -/
theorem splitPullback_isFlatOver
    [HasWeakSheafify (Opens.grothendieckTopology X3) CommRingCat.{u}]
    [(Opens.grothendieckTopology X3).WEqualsLocallyBijective CommRingCat.{u}]
    (σ : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :
    SheafOfModules.IsFlatOver (((canonicalSplitting σ) ^*).obj (moduleRestrict σ)) σ.f1' := sorry

/-- The inverse image `h^* F'_2` is flat over `S'_1`. -/
theorem homPullback_isFlatOver (σ : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :
    SheafOfModules.IsFlatOver ((σ.h.hom ^*).obj σ.module) σ.f1' := sorry

/-- The stored module `F'_2` as a flat lift of `F` along `(f, f'_2)`. -/
noncomputable def moduleLift (σ : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :
    FlatLift (thickeningHom2 σ) (moduleRestrict σ : X.Modules) :=
  let g := thickeningHom2 σ
  let F := moduleRestrict σ
  FlatLift.of g F σ.module
    (eqToIso (congrArg (fun (φ : X ⟶ X2) ↦ (φ ^*).obj σ.module)
      (Thickening.of_hom i2))) σ.module_isFlatOver

/-- The middle module of `moduleLift` is the stored `𝒪'_2`-module. -/
theorem moduleLift_module (σ : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :
    (moduleLift σ).module = σ.module := sorry

/-- Inverse image of `F'_2` along the bundled thickening recovers `F`. -/
def moduleLift_sourceRestrict (σ : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :=
  (moduleLift σ).restrictIso

/-- The inverse image `π^* F` of the restriction `F = F'_2|_X`, as a flat lift along
`(f, f'_1)`. -/
noncomputable def splitPullback
    [HasWeakSheafify (Opens.grothendieckTopology X3) CommRingCat.{u}]
    [(Opens.grothendieckTopology X3).WEqualsLocallyBijective CommRingCat.{u}]
    (σ : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :
    FlatLift (thickeningHom1 σ) (moduleRestrict σ : X.Modules) :=
  let g := thickeningHom1 σ
  let F := moduleRestrict σ
  let F' := ((canonicalSplitting σ) ^*).obj F
  FlatLift.of g F F'
    (eqToIso (congrArg (fun (φ : X ⟶ X1) ↦ (φ ^*).obj F')
      (Thickening.of_hom i1)) ≪≫
      (pullbackCompIso i1 (canonicalSplitting σ)).symm.app F ≪≫
      eqToIso (congrArg (fun (φ : X ⟶ X) ↦ (φ ^*).obj F)
        (canonicalSplitting_leftInv σ)) ≪≫
      (pullbackIdIso X).app F)
    (splitPullback_isFlatOver σ)

/-- The middle module of `splitPullback` is `π^* F`. -/
theorem splitPullback_module
    [HasWeakSheafify (Opens.grothendieckTopology X3) CommRingCat.{u}]
    [(Opens.grothendieckTopology X3).WEqualsLocallyBijective CommRingCat.{u}]
    (σ : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :
    (splitPullback σ).module = ((canonicalSplitting σ) ^*).obj (moduleRestrict σ) := sorry

/-- Inverse image of `π^* F` along `i1` recovers `F`. -/
theorem splitPullback_restrictIso
    [HasWeakSheafify (Opens.grothendieckTopology X3) CommRingCat.{u}]
    [(Opens.grothendieckTopology X3).WEqualsLocallyBijective CommRingCat.{u}]
    (σ : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :
    Nonempty ((i1 ^*).obj (splitPullback σ).module ≅ moduleRestrict σ) := sorry

/-- Inverse image of `π^* F` along the bundled thickening recovers `F`. -/
def splitPullback_sourceRestrict
    [HasWeakSheafify (Opens.grothendieckTopology X3) CommRingCat.{u}]
    [(Opens.grothendieckTopology X3).WEqualsLocallyBijective CommRingCat.{u}]
    (σ : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :=
  (splitPullback σ).restrictIso

/-- The inverse image `h^* F'_2`, as a flat lift along `(f, f'_1)`. -/
noncomputable def homPullback (σ : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :
    FlatLift (thickeningHom1 σ) (moduleRestrict σ : X.Modules) :=
  let g := thickeningHom1 σ
  let F := moduleRestrict σ
  let F' := (σ.h.hom ^*).obj σ.module
  FlatLift.of g F F'
    (eqToIso (congrArg (fun (φ : X ⟶ X1) ↦ (φ ^*).obj F')
      (Thickening.of_hom i1)) ≪≫
      (pullbackCompIso i1 σ.h.hom).symm.app σ.module ≪≫
      eqToIso (congrArg (fun (φ : X ⟶ X2) ↦ (φ ^*).obj σ.module) σ.h.w))
    (homPullback_isFlatOver σ)

/-- The middle module of `homPullback` is `h^* F'_2`. -/
theorem homPullback_module (σ : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :
    (homPullback σ).module = (σ.h.hom ^*).obj σ.module := sorry

/-- Inverse image of `h^* F'_2` along `i1` recovers `F`. -/
theorem homPullback_restrictIso (σ : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :
    Nonempty ((i1 ^*).obj (homPullback σ).module ≅ moduleRestrict σ) := sorry

/-- Inverse image of `h^* F'_2` along the bundled thickening recovers `F`. -/
def homPullback_sourceRestrict (σ : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :=
  (homPullback σ).restrictIso

/-- The split pullback is flat over the first thickened base and restricts to the original module. -/
theorem splitPullback_spec
    [HasWeakSheafify (Opens.grothendieckTopology X3) CommRingCat.{u}]
    [(Opens.grothendieckTopology X3).WEqualsLocallyBijective CommRingCat.{u}]
    (σ : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :
    SheafOfModules.IsFlatOver (splitPullback σ).module σ.f1' ∧
      Nonempty ((i1 ^*).obj (splitPullback σ).module ≅ moduleRestrict σ) := sorry

/-- The pullback of the middle module is flat over the first thickened base and restricts to the original module. -/
theorem homPullback_spec (σ : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :
    SheafOfModules.IsFlatOver (homPullback σ).module σ.f1' ∧
      Nonempty ((i1 ^*).obj (homPullback σ).module ≅ moduleRestrict σ) := sorry

end SesFlatThickenings
end IsFirstOrderThickening
end AlgebraicGeometry.RingedSpace
