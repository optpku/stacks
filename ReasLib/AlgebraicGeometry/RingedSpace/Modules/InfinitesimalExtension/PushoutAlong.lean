module

public import ReasLib.AlgebraicGeometry.RingedSpace.Modules.InfinitesimalExtension.Pushout
public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.Hom

/-!
# Pushouts along commuting triangles of first-order thickenings

Compatibility of infinitesimal maps and pushout constructions transport along the
triangle identity of a morphism of first-order thickenings.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.IsFirstOrderThickening hiding Hom
open AlgebraicGeometry.RingedSpace.Modules
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Modules
namespace InfinitesimalExtension

variable {X : RingedSpace.{u}}

/-- The infinitesimal-map square of `cb` over `ca` along a triangle `ia ≫ h = ib`. -/
abbrev infinitesimalMapCommSqAlong
    {Xa Xb : RingedSpace.{u}} {ia : X ⟶ Xa} {ib : X ⟶ Xb}
    [IsFirstOrderThickening ia] [IsFirstOrderThickening ib]
    (h : Xa ⟶ Xb) (w : ia ≫ h = ib) {F Ka Kb : X.Modules}
    (ca : kernelIdealSheaf ia ⊗ (ia _*).obj F ⟶ (ia _*).obj Ka)
    (cb : kernelIdealSheaf ib ⊗ (ib _*).obj F ⟶ (ib _*).obj Kb)
    (κ : Kb ⟶ Ka) : Prop :=
  (@Eq.rec (X ⟶ Xb) (ia ≫ h)
      (fun ib _w ↦
        [IsFirstOrderThickening ib] →
          (kernelIdealSheaf ib ⊗ (ib _*).obj F ⟶ (ib _*).obj Kb) →
          (Kb ⟶ Ka) → Prop)
      (fun [IsFirstOrderThickening (ia ≫ h)] cb κ ↦ infinitesimalMapCommSq ca cb κ)
      ib w)
    cb κ

/-- The triangle-adapted square is commutativity of the restricted infinitesimal maps
`ℐᵢ ⊗ ℱ ⟶ 𝒦ᵢ` against `κ` and the kernel-ideal map of `h`. -/
theorem infinitesimalMapCommSqAlong_iff
    {Xa Xb : RingedSpace.{u}} {ia : X ⟶ Xa} {ib : X ⟶ Xb}
    [IsFirstOrderThickening ia] [IsFirstOrderThickening ib]
    (h : Xa ⟶ Xb) (w : ia ≫ h = ib) {F Ka Kb : X.Modules}
    (ca : kernelIdealSheaf ia ⊗ (ia _*).obj F ⟶ (ia _*).obj Ka)
    (cb : kernelIdealSheaf ib ⊗ (ib _*).obj F ⟶ (ib _*).obj Kb)
    (κ : Kb ⟶ Ka) :
    infinitesimalMapCommSqAlong h w ca cb κ ↔
      infinitesimalMap_restrict ib cb ≫ κ =
        tensorHom (idealMap h w) (𝟙 F) ≫ infinitesimalMap_restrict ia ca :=
  sorry

variable {X1 X2 : RingedSpace.{u}}
variable {i1 : X ⟶ X1} {i2 : X ⟶ X2}
variable [IsFirstOrderThickening i1] [IsFirstOrderThickening i2]

/-- Pushout of an infinitesimal extension along a morphism of first-order thickenings
and a compatible map of kernels. -/
noncomputable def pushoutAlong (f : IsFirstOrderThickening.Hom i1 i2)
    {F K1 K2 : X.Modules}
    (c1 : kernelIdealSheaf i1 ⊗ (i1 _*).obj F ⟶ (i1 _*).obj K1)
    (c2 : kernelIdealSheaf i2 ⊗ (i2 _*).obj F ⟶ (i2 _*).obj K2)
    (κ : K2 ⟶ K1) (hc : infinitesimalMapCommSqAlong f.hom f.w c1 c2 κ)
    (E2 : InfinitesimalExtension i2 F K2 c2) :
    InfinitesimalExtension i1 F K1 c1 :=
  (@Eq.rec (X ⟶ X2) (i1 ≫ f.hom)
      (fun i2 w ↦
        [IsFirstOrderThickening i2] →
          (c2 : kernelIdealSheaf i2 ⊗ (i2 _*).obj F ⟶ (i2 _*).obj K2) →
          infinitesimalMapCommSqAlong f.hom w c1 c2 κ →
          InfinitesimalExtension i2 F K2 c2 →
          InfinitesimalExtension i1 F K1 c1)
      (fun [IsFirstOrderThickening (i1 ≫ f.hom)] _ hc E2 ↦ pushout c1 κ hc E2)
      i2 f.w)
    c2 hc E2

/-- The pushout along a morphism of first-order thickenings is short exact and has
the prescribed infinitesimal map. -/
theorem pushoutAlong_spec (f : IsFirstOrderThickening.Hom i1 i2)
    {F K1 K2 : X.Modules}
    (c1 : kernelIdealSheaf i1 ⊗ (i1 _*).obj F ⟶ (i1 _*).obj K1)
    (c2 : kernelIdealSheaf i2 ⊗ (i2 _*).obj F ⟶ (i2 _*).obj K2)
    (κ : K2 ⟶ K1) (hc : infinitesimalMapCommSqAlong f.hom f.w c1 c2 κ)
    (E2 : InfinitesimalExtension i2 F K2 c2) :
    let E := pushoutAlong f c1 c2 κ hc E2
    (ShortComplex.mk E.ι E.π E.w).ShortExact ∧
      infinitesimalMap i1 E.ι E.π E.w E.shortExact = c1 :=
  spec (pushoutAlong f c1 c2 κ hc E2)

end InfinitesimalExtension
end AlgebraicGeometry.RingedSpace.Modules
