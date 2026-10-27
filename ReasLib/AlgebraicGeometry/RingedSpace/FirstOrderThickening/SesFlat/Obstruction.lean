/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FlatLift.RelativeTorsor
public import ReasLib.AlgebraicGeometry.RingedSpace.Morphism.Thickening.FlatLift.Obstruction
public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.SesFlat.Lift

/-!
# Difference class `θ` and the tensored kernel sequence

The difference of `h^* F'_2` against `π^* F` is an `Ext¹` class
`θ` with coefficients `f^* 𝒥₁ ⊗ F`. The maps `f^* 𝒥ᵢ ⊗ F` form the short
complex whose connecting map sends `θ` to the relative existence obstruction
on `X'_3`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory TopologicalSpace
open CategoryTheory.Abelian (Ext)
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace (Modules)
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Modules
open AlgebraicGeometry.RingedSpace.Modules.InfinitesimalExtension
open AlgebraicGeometry.RingedSpace.Thickening.Hom (FlatLift)
open AlgebraicGeometry.RingedSpace.Thickening.Hom.FlatLift
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.IsFirstOrderThickening
namespace SesFlatThickenings

variable {X S X1 X2 X3 S1 S2 S3 : RingedSpace.{u}}
variable {f : X ⟶ S} {i1 : X ⟶ X1} {i2 : X ⟶ X2} {i3 : X ⟶ X3}
variable {t1 : S ⟶ S1} {t2 : S ⟶ S2} {t3 : S ⟶ S3}
variable [IsFirstOrderThickening i1] [IsFirstOrderThickening i2]
variable [IsFirstOrderThickening i3] [IsFirstOrderThickening t1]
variable [IsFirstOrderThickening t2] [IsFirstOrderThickening t3]

/-- The two maps `f^* 𝒥₃ ⊗ F ⟶ f^* 𝒥₂ ⊗ F ⟶ f^* 𝒥₁ ⊗ F` compose to zero. -/
theorem sourceIdealTensor_comp_zero (σ : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :
    tensorHom ((f ^*).map σ.base'.idealMap) (𝟙 (moduleRestrict σ)) ≫
      tensorHom ((f ^*).map σ.base.idealMap) (𝟙 (moduleRestrict σ)) = 0 := sorry

/-- The short complex `f^* 𝒥₃ ⊗ F ⟶ f^* 𝒥₂ ⊗ F ⟶ f^* 𝒥₁ ⊗ F`. -/
noncomputable def sourceIdealTensorShortComplex
    (σ : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :
    ShortComplex X.Modules :=
  ShortComplex.mk
    (tensorHom ((f ^*).map σ.base'.idealMap) (𝟙 (moduleRestrict σ)))
    (tensorHom ((f ^*).map σ.base.idealMap) (𝟙 (moduleRestrict σ)))
    (sourceIdealTensor_comp_zero σ)

/-- The tensored kernel sequence is short exact. -/
theorem sourceIdealTensor_shortExact (σ : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :
    (sourceIdealTensorShortComplex σ).ShortExact := sorry

/-- The relative infinitesimal extension of a flat lift along the first vertical pair,
with the diagram's strictness and flatness proofs. -/
noncomputable def toRelative1 (σ : SesFlatThickenings f i1 i2 i3 t1 t2 t3)
    (L : FlatLift (thickeningHom1 σ) (moduleRestrict σ : X.Modules)) :=
  let g := thickeningHom1 σ
  let F := moduleRestrict σ
  @toRelativeInfinitesimalExtension (Thickening.of i1) (Thickening.of t1)
    (isFirstOrderThickening_ofHom i1) (isFirstOrderThickening_ofHom t1)
    g F σ.strict1 (moduleRestrict_isFlatOver σ) σ.flat1 L

/-- The based equivalence between extension classes and relative infinitesimal extension
classes along the first vertical pair. -/
noncomputable def sourceIdealIsoClassEquiv1
    (σ : SesFlatThickenings f i1 i2 i3 t1 t2 t3)
    (L0 : FlatLift (thickeningHom1 σ) (moduleRestrict σ : X.Modules)) :=
  let g := thickeningHom1 σ
  let F := moduleRestrict σ
  @sourceIdealIsoClassEquiv (Thickening.of i1) (Thickening.of t1)
    (isFirstOrderThickening_ofHom i1) (isFirstOrderThickening_ofHom t1)
    g F σ.strict1 (moduleRestrict_isFlatOver σ) σ.flat1 L0

/-- The middle module of `toRelative1` is the lifted module. -/
theorem toRelative1_module (σ : SesFlatThickenings f i1 i2 i3 t1 t2 t3)
    (L : FlatLift (thickeningHom1 σ) (moduleRestrict σ : X.Modules)) :
    (toRelative1 σ L).module = L.module := sorry

/-- The zero class is sent to the relative infinitesimal extension of the chosen lift. -/
theorem sourceIdealIsoClassEquiv1_zero (σ : SesFlatThickenings f i1 i2 i3 t1 t2 t3)
    (L0 : FlatLift (thickeningHom1 σ) (moduleRestrict σ : X.Modules)) :
    sourceIdealIsoClassEquiv1 σ L0 0 = IsoClass.mk (toRelative1 σ L0) := sorry

/-- The relative infinitesimal extension attached to `h^* F'_2`. -/
noncomputable def homPullbackRelative (σ : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :=
  toRelative1 σ (homPullback σ)

/-- The middle module of `homPullbackRelative` is `h^* F'_2`. -/
theorem homPullbackRelative_module (σ : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :
    (homPullbackRelative σ).module = (homPullback σ).module := sorry

/-- The relative infinitesimal extension attached to `π^* F`. -/
noncomputable def splitPullbackRelative
    [HasWeakSheafify (Opens.grothendieckTopology X3) CommRingCat.{u}]
    [(Opens.grothendieckTopology X3).WEqualsLocallyBijective CommRingCat.{u}]
    (σ : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :=
  toRelative1 σ (splitPullback σ)

/-- The middle module of `splitPullbackRelative` is `π^* F`. -/
theorem splitPullbackRelative_module
    [HasWeakSheafify (Opens.grothendieckTopology X3) CommRingCat.{u}]
    [(Opens.grothendieckTopology X3).WEqualsLocallyBijective CommRingCat.{u}]
    (σ : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :
    (splitPullbackRelative σ).module = (splitPullback σ).module := sorry

/-- The based chart with basepoint `π^* F`. -/
noncomputable def sourceIdealIsoClassEquiv_split
    [HasWeakSheafify (Opens.grothendieckTopology X3) CommRingCat.{u}]
    [(Opens.grothendieckTopology X3).WEqualsLocallyBijective CommRingCat.{u}]
    (σ : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :=
  sourceIdealIsoClassEquiv1 σ (splitPullback σ)

/-- The relative identity infinitesimal comparison along `(f, f'_3)`. -/
noncomputable def relativeIdentityInfinitesimalMap3
    (σ : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :=
  let g := thickeningHom3 σ
  let F := moduleRestrict σ
  @relativeIdentityInfinitesimalMap (Thickening.of i3) (Thickening.of t3)
    (isFirstOrderThickening_ofHom i3) (isFirstOrderThickening_ofHom t3)
    g σ.strict3 σ.flat3 F

/-- The zero class is sent to the relative infinitesimal extension of `π^* F`. -/
theorem sourceIdealIsoClassEquiv_split_zero
    [HasWeakSheafify (Opens.grothendieckTopology X3) CommRingCat.{u}]
    [(Opens.grothendieckTopology X3).WEqualsLocallyBijective CommRingCat.{u}]
    (σ : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :
    sourceIdealIsoClassEquiv1 σ (splitPullback σ) 0 =
      IsoClass.mk (toRelative1 σ (splitPullback σ)) := sorry

/-- The third relative identity comparison is the canonical identity comparison
for the third vertical pair. -/
theorem relativeIdentityInfinitesimalMap3_eq
    (σ : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :
    relativeIdentityInfinitesimalMap3 σ =
      let g := thickeningHom3 σ
      let F := moduleRestrict σ
      @relativeIdentityInfinitesimalMap (Thickening.of i3) (Thickening.of t3)
        (isFirstOrderThickening_ofHom i3) (isFirstOrderThickening_ofHom t3)
        g σ.strict3 σ.flat3 F := sorry

/-- The existence obstruction to lifting `F` to an `𝒪'_3`-module
flat over `S'_3`, as a class in `Ext F (f^* 𝒥₃ ⊗ F) 2`. -/
noncomputable def existenceObstruction3 [HasExt.{u} X.Modules]
    (σ : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :
    Ext (moduleRestrict σ) ((f ^*).obj (idealModule t3) ⊗ moduleRestrict σ) 2 :=
  let g := thickeningHom3 σ
  let F := moduleRestrict σ
  existenceObstruction (Thickening.of i3).hom F
    ((g.left ^*).obj (idealModule (Thickening.of t3).hom) ⊗ F)
    (relativeIdentityInfinitesimalMap3 σ)

/-- `existenceObstruction3` is the canonical relative identity obstruction along `(f, f'_3)`. -/
theorem existenceObstruction3_eq [HasExt.{u} X.Modules]
    (σ : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :
    existenceObstruction3 σ =
      let g := thickeningHom3 σ
      let F := moduleRestrict σ
      existenceObstruction (Thickening.of i3).hom F
        ((g.left ^*).obj (idealModule (Thickening.of t3).hom) ⊗ F)
        (relativeIdentityInfinitesimalMap3 σ) := sorry

/-- The difference class `θ ∈ Ext F (f^* 𝒥₁ ⊗ F) 1` of `h^* F'_2` against `π^* F`. -/
noncomputable def theta
    [HasWeakSheafify (Opens.grothendieckTopology X3) CommRingCat.{u}]
    [(Opens.grothendieckTopology X3).WEqualsLocallyBijective CommRingCat.{u}]
    [HasExt.{u} X.Modules]
    (σ : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :
    Ext (moduleRestrict σ) ((f ^*).obj (idealModule t1) ⊗ moduleRestrict σ) 1 :=
  ExtensionClass.toExt
    ((sourceIdealIsoClassEquiv_split σ).symm (IsoClass.mk (homPullbackRelative σ)))

/-- The difference class is the Ext¹ image of the inverse chart based at the split pullback. -/
theorem theta_eq
    [HasWeakSheafify (Opens.grothendieckTopology X3) CommRingCat.{u}]
    [(Opens.grothendieckTopology X3).WEqualsLocallyBijective CommRingCat.{u}]
    [HasExt.{u} X.Modules]
    (σ : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :
    theta σ =
      ExtensionClass.toExt
        ((sourceIdealIsoClassEquiv_split σ).symm
          (IsoClass.mk (homPullbackRelative σ))) := sorry

/-- The Yoneda boundary of the difference class is the relative identity obstruction on the third thickening. -/
theorem theta_comp_eq_existenceObstruction
    [HasWeakSheafify (Opens.grothendieckTopology X3) CommRingCat.{u}]
    [(Opens.grothendieckTopology X3).WEqualsLocallyBijective CommRingCat.{u}]
    [HasExt.{u} X.Modules]
    (σ : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :
    (theta σ).comp (sourceIdealTensor_shortExact σ).extClass (rfl : 1 + 1 = 2) =
      existenceObstruction3 σ := sorry

end SesFlatThickenings
end AlgebraicGeometry.RingedSpace.IsFirstOrderThickening
