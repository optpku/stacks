module

public import stacks_project.Chap91.Lemma_91_6_3_Lift
public import stacks_project.Chap91.Lemma_91_6_3_Obstruction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Difference of `π^* F` and `h^* F'_2` versus the relative existence obstruction

In Situation 91.6.2, both `π^* F` and `h^* F'_2` are flat lifts of `F` along
`(f, f'_1)`. Their Lemma 91.6.1 difference is a class `θ` in
`Ext F (f^* 𝒥₁ ⊗ F) 1` whose connecting image in `Ext F (f^* 𝒥₃ ⊗ F) 2` is the
obstruction to lifting `F` to an `𝒪'_3`-module flat over `S'_3`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory TopologicalSpace
open CategoryTheory.Abelian (Ext)
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace (Modules)
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Modules
open AlgebraicGeometry.RingedSpace.Modules.InfinitesimalExtension
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

/-- Lemma 91.6.3 (1) In Situation 91.6.2, `π^* F` is an `𝒪'_1`-module flat over `S'_1`
restricting to `F` on `X`. -/
@[stacks 08VT]
theorem splitPullback_spec
    [HasWeakSheafify (Opens.grothendieckTopology X3) CommRingCat.{u}]
    [(Opens.grothendieckTopology X3).WEqualsLocallyBijective CommRingCat.{u}]
    (σ : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :
    SheafOfModules.IsFlatOver (splitPullback σ).module σ.f1' ∧
      Nonempty ((i1 ^*).obj (splitPullback σ).module ≅ moduleRestrict σ) := sorry

/-- Lemma 91.6.3 (2) In Situation 91.6.2, `h^* F'_2` is an `𝒪'_1`-module flat over `S'_1`
restricting to `F` on `X`. -/
@[stacks 08VT]
theorem homPullback_spec (σ : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :
    SheafOfModules.IsFlatOver (homPullback σ).module σ.f1' ∧
      Nonempty ((i1 ^*).obj (homPullback σ).module ≅ moduleRestrict σ) := sorry

/-- Lemma 91.6.3 (3) In Situation 91.6.2, the Lemma 91.6.1 difference of `h^* F'_2`
against `π^* F` is the class `θ` of `Ext F (f^* 𝒥₁ ⊗ F) 1`. -/
@[stacks 08VT]
theorem theta_eq
    [HasWeakSheafify (Opens.grothendieckTopology X3) CommRingCat.{u}]
    [(Opens.grothendieckTopology X3).WEqualsLocallyBijective CommRingCat.{u}]
    [HasExt.{u} X.Modules]
    (σ : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :
    theta σ =
      ExtensionClass.toExt
        ((sourceIdealIsoClassEquiv_split σ).symm
          (IsoClass.mk (homPullbackRelative σ))) := sorry

/-- Lemma 91.6.3 (4) In Situation 91.6.2, the connecting map of
`0 ⟶ f^* 𝒥₃ ⊗ F ⟶ f^* 𝒥₂ ⊗ F ⟶ f^* 𝒥₁ ⊗ F ⟶ 0` sends `θ` to the Lemma 91.6.1
obstruction to lifting `F` to an `𝒪'_3`-module flat over `S'_3`. -/
@[stacks 08VT]
theorem theta_comp_eq_existenceObstruction
    [HasWeakSheafify (Opens.grothendieckTopology X3) CommRingCat.{u}]
    [(Opens.grothendieckTopology X3).WEqualsLocallyBijective CommRingCat.{u}]
    [HasExt.{u} X.Modules]
    (σ : SesFlatThickenings f i1 i2 i3 t1 t2 t3) :
    (theta σ).comp (sourceIdealTensor_shortExact σ).extClass (rfl : 1 + 1 = 2) =
      existenceObstruction3 σ := sorry

end SesFlatThickenings
end AlgebraicGeometry.RingedSpace.IsFirstOrderThickening
