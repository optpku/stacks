module

public import stacks_project.Chap91.Lemma_91_4_4_Obstruction
public import stacks_project.Chap91.Remark_91_4_6
public import stacks_project.Chap91.Remark_91_4_7
public import stacks_project.Chap91.Remark_91_4_9
import Mathlib.Tactic.CrossRefAttribute

/-!
# Connecting map of a kernel SES versus the existence obstruction

Along a complex of first-order thickenings of a ringed space, an 08L4 extension on the
middle thickening pushes out to the first thickening. Its `Ext¹` class, formed using the
canonical trivialization, is sent by the connecting map of a kernel short exact sequence
to the existence obstruction on the last thickening.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.Abelian (Ext)
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

variable {X1 X2 X3 : RingedSpace.{u}}
variable {i1 : X ⟶ X1} {i2 : X ⟶ X2} {i3 : X ⟶ X3}
variable [IsFirstOrderThickening i1] [IsFirstOrderThickening i2]
variable [IsFirstOrderThickening i3]

/-- The canonical splitting of the first thickening in a complex of first-order thickenings,
packaged as the trivialization consumed by `extClass`. -/
noncomputable def canonicalSplit (f : IsFirstOrderThickening.Hom i1 i2)
    (g : IsFirstOrderThickening.Hom i2 i3) (hC : IsComplex f g)
    [HasWeakSheafify (Opens.grothendieckTopology X3) CommRingCat.{u}]
    [(Opens.grothendieckTopology X3).WEqualsLocallyBijective CommRingCat.{u}] :
    Trivialization i1 :=
  Trivialization.ofRetraction (canonicalTrivialization f g hC)
    (canonicalTrivialization_leftInv f g hC)

/-- The underlying retraction of `canonicalSplit` is the canonical trivialization of
Remark 91.4.9. -/
theorem canonicalSplit_retraction (f : IsFirstOrderThickening.Hom i1 i2)
    (g : IsFirstOrderThickening.Hom i2 i3) (hC : IsComplex f g)
    [HasWeakSheafify (Opens.grothendieckTopology X3) CommRingCat.{u}]
    [(Opens.grothendieckTopology X3).WEqualsLocallyBijective CommRingCat.{u}] :
    (canonicalSplit f g hC).retraction = canonicalTrivialization f g hC :=
  sorry

/-- Pushout of an 08L4 extension along a triangle `i₁ ≫ h = i₂`, after identifying
the middle thickening with `i₁ ≫ h`. -/
noncomputable def pushoutAlong_of (h : X1 ⟶ X2) (w : i1 ≫ h = i2)
    {F K1 K2 : X.Modules}
    (c1 : kernelIdealSheaf i1 ⊗ (i1 _*).obj F ⟶ (i1 _*).obj K1)
    (c2 : kernelIdealSheaf i2 ⊗ (i2 _*).obj F ⟶ (i2 _*).obj K2)
    (κ : K2 ⟶ K1) (hc : infinitesimalMapCommSqAlong h w c1 c2 κ)
    (E2 : InfinitesimalExtension i2 F K2 c2) :
    InfinitesimalExtension i1 F K1 c1 :=
  (@Eq.rec (X ⟶ X2) (i1 ≫ h)
      (fun i2 w ↦
        [IsFirstOrderThickening i2] →
          (c2 : kernelIdealSheaf i2 ⊗ (i2 _*).obj F ⟶ (i2 _*).obj K2) →
          infinitesimalMapCommSqAlong h w c1 c2 κ →
          InfinitesimalExtension i2 F K2 c2 →
          InfinitesimalExtension i1 F K1 c1)
      (fun [IsFirstOrderThickening (i1 ≫ h)] _ hc E2 ↦ pushout c1 κ hc E2)
      i2 w)
    c2 hc E2

/-- The 08L4 extension `ℱ'₁` on `X'₁` obtained by pushing out `ℱ'₂` along `κ₂₁`, using
the functoriality of Remark 91.4.7. -/
noncomputable def pushoutAlong (f : IsFirstOrderThickening.Hom i1 i2)
    {F K1 K2 : X.Modules}
    (c1 : kernelIdealSheaf i1 ⊗ (i1 _*).obj F ⟶ (i1 _*).obj K1)
    (c2 : kernelIdealSheaf i2 ⊗ (i2 _*).obj F ⟶ (i2 _*).obj K2)
    (κ : K2 ⟶ K1) (hc : infinitesimalMapCommSqAlong f.hom f.w c1 c2 κ)
    (E2 : InfinitesimalExtension i2 F K2 c2) :
    InfinitesimalExtension i1 F K1 c1 :=
  pushoutAlong_of f.hom f.w c1 c2 κ hc E2

/-- `pushoutAlong` is the triangle-identity transport of `pushoutAlong_of`. -/
theorem pushoutAlong_eq_of (f : IsFirstOrderThickening.Hom i1 i2)
    {F K1 K2 : X.Modules}
    (c1 : kernelIdealSheaf i1 ⊗ (i1 _*).obj F ⟶ (i1 _*).obj K1)
    (c2 : kernelIdealSheaf i2 ⊗ (i2 _*).obj F ⟶ (i2 _*).obj K2)
    (κ : K2 ⟶ K1) (hc : infinitesimalMapCommSqAlong f.hom f.w c1 c2 κ)
    (E2 : InfinitesimalExtension i2 F K2 c2) :
    pushoutAlong f c1 c2 κ hc E2 = pushoutAlong_of f.hom f.w c1 c2 κ hc E2 :=
  sorry

/-- The pushout along a thickening morphism is an 08L4 extension with infinitesimal map
`c₁`. -/
theorem pushoutAlong_spec (f : IsFirstOrderThickening.Hom i1 i2)
    {F K1 K2 : X.Modules}
    (c1 : kernelIdealSheaf i1 ⊗ (i1 _*).obj F ⟶ (i1 _*).obj K1)
    (c2 : kernelIdealSheaf i2 ⊗ (i2 _*).obj F ⟶ (i2 _*).obj K2)
    (κ : K2 ⟶ K1) (hc : infinitesimalMapCommSqAlong f.hom f.w c1 c2 κ)
    (E2 : InfinitesimalExtension i2 F K2 c2) :
    let E := pushoutAlong f c1 c2 κ hc E2
    (ShortComplex.mk E.ι E.π E.w).ShortExact ∧
      infinitesimalMap i1 E.ι E.π E.w E.shortExact = c1 :=
  sorry

/-- The class `ξ_{ℱ'₁}` in `Ext ℱ 𝒦₁ 1` obtained from the pushed-out extension by
restriction of scalars along the canonical splitting. -/
noncomputable def extClass_pushoutAlong (f : IsFirstOrderThickening.Hom i1 i2)
    (g : IsFirstOrderThickening.Hom i2 i3) (hC : IsComplex f g)
    [HasWeakSheafify (Opens.grothendieckTopology X3) CommRingCat.{u}]
    [(Opens.grothendieckTopology X3).WEqualsLocallyBijective CommRingCat.{u}]
    [HasExt.{u} X.Modules]
    {F K1 K2 : X.Modules}
    (c1 : kernelIdealSheaf i1 ⊗ (i1 _*).obj F ⟶ (i1 _*).obj K1)
    (c2 : kernelIdealSheaf i2 ⊗ (i2 _*).obj F ⟶ (i2 _*).obj K2)
    (κ : K2 ⟶ K1) (hc : infinitesimalMapCommSqAlong f.hom f.w c1 c2 κ)
    (E2 : InfinitesimalExtension i2 F K2 c2) :
    Ext F K1 1 :=
  extClass (canonicalSplit f g hC) (pushoutAlong f c1 c2 κ hc E2)

/-- `extClass_pushoutAlong` is the `extClass` of the pushed-out extension along the
canonical splitting. -/
theorem extClass_pushoutAlong_eq (f : IsFirstOrderThickening.Hom i1 i2)
    (g : IsFirstOrderThickening.Hom i2 i3) (hC : IsComplex f g)
    [HasWeakSheafify (Opens.grothendieckTopology X3) CommRingCat.{u}]
    [(Opens.grothendieckTopology X3).WEqualsLocallyBijective CommRingCat.{u}]
    [HasExt.{u} X.Modules]
    {F K1 K2 : X.Modules}
    (c1 : kernelIdealSheaf i1 ⊗ (i1 _*).obj F ⟶ (i1 _*).obj K1)
    (c2 : kernelIdealSheaf i2 ⊗ (i2 _*).obj F ⟶ (i2 _*).obj K2)
    (κ : K2 ⟶ K1) (hc : infinitesimalMapCommSqAlong f.hom f.w c1 c2 κ)
    (E2 : InfinitesimalExtension i2 F K2 c2) :
    extClass_pushoutAlong f g hC c1 c2 κ hc E2 =
      extClass (canonicalSplit f g hC) (pushoutAlong f c1 c2 κ hc E2) :=
  sorry

/-- Remark 91.4.10 Let `(X, 𝒪_X)` be a ringed space and let `ℱ` be an `𝒪_X`-module. Let
`X'₁ ⟶ X'₂ ⟶ X'₃` be a complex of first-order thickenings of `X`, see Remark 91.4.9, and
let `(𝒦ᵢ, cᵢ)` for `i = 1, 2, 3` be pairs consisting of an `𝒪_X`-module `𝒦ᵢ` and a map
`cᵢ : ℐᵢ ⊗_{𝒪_X} ℱ ⟶ 𝒦ᵢ` (recovered from the kernel-ideal pushforward form by
`infinitesimalMap_restrict`). Assume given a short exact sequence
`0 ⟶ 𝒦₃ ⟶ 𝒦₂ ⟶ 𝒦₁ ⟶ 0` of `𝒪_X`-modules making the two infinitesimal-map squares
commute, and an 08L4 extension `ℱ'₂` of `ℱ` by `𝒦₂` with `c_{ℱ'₂} = c₂`. Functoriality
of Remark 91.4.7 supplies `ℱ'₁` on `X'₁`, and Remark 91.4.6 with the canonical splitting
`π : X'₁ ⟶ X` of Remark 91.4.9 supplies `ξ_{ℱ'₁}` in `Ext ℱ 𝒦₁ 1`. The connecting map
`∂ : Ext ℱ 𝒦₁ 1 ⟶ Ext ℱ 𝒦₃ 2` of the kernel sequence sends `ξ_{ℱ'₁}` to the existence
obstruction `o(ℱ, 𝒦₃, c₃)` of Lemma 91.4.4. -/
@[stacks 08LF]
theorem connecting_extClass_eq_existenceObstruction
    (f : IsFirstOrderThickening.Hom i1 i2) (g : IsFirstOrderThickening.Hom i2 i3)
    (hC : IsComplex f g)
    [HasWeakSheafify (Opens.grothendieckTopology X3) CommRingCat.{u}]
    [(Opens.grothendieckTopology X3).WEqualsLocallyBijective CommRingCat.{u}]
    [HasExt.{u} X.Modules]
    {F K1 K2 K3 : X.Modules}
    (c1 : kernelIdealSheaf i1 ⊗ (i1 _*).obj F ⟶ (i1 _*).obj K1)
    (c2 : kernelIdealSheaf i2 ⊗ (i2 _*).obj F ⟶ (i2 _*).obj K2)
    (c3 : kernelIdealSheaf i3 ⊗ (i3 _*).obj F ⟶ (i3 _*).obj K3)
    (κ32 : K3 ⟶ K2) (κ21 : K2 ⟶ K1) (w : κ32 ≫ κ21 = 0)
    (hκ : (ShortComplex.mk κ32 κ21 w).ShortExact)
    (hc12 : infinitesimalMapCommSqAlong f.hom f.w c1 c2 κ21)
    (hc23 : infinitesimalMapCommSqAlong g.hom g.w c2 c3 κ32)
    (E2 : InfinitesimalExtension i2 F K2 c2) :
    (extClass_pushoutAlong f g hC c1 c2 κ21 hc12 E2).comp hκ.extClass (rfl : 1 + 1 = 2) =
      existenceObstruction i3 F K3 c3 :=
  sorry

end InfinitesimalExtension
end AlgebraicGeometry.RingedSpace.Modules
