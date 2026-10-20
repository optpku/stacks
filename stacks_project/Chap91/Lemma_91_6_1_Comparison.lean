/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FlatMorphism
public import stacks_project.Chap91.Lemma_91_5_2
public import stacks_project.Chap91.Lemma_91_5_6_Lift
public import stacks_project.Chap91.Lemma_91_5_7_Comparison
public import stacks_project.Chap91.Situation_91_6_2_Diagram

/-!
# Identification `ℐ = f^* 𝒥` along a strict flat first-order thickening

If `(f, f')` is a strict morphism of first-order thickenings and `f'` is flat, the
kernel-ideal comparison `f^* 𝒥 ⟶ ℐ` is an isomorphism. Transporting the identity
infinitesimal map of Lemma 91.4.4 along this identification yields the relative
comparison `c = 1` with coefficients `f^* 𝒥 ⊗ F`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace (Modules)
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Modules
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Thickening.Hom

variable {T U : Thickening.{u}} [IsFirstOrderThickening T.hom] [IsFirstOrderThickening U.hom]
variable {g : T ⟶ U}

/-- Along a strict morphism of first-order thickenings with `f'` flat, the comparison
`f^* 𝒥 ⟶ ℐ` is an isomorphism. -/
theorem isIso_sourceIdealMap (hg : IsStrict g) [RingedSpace.Hom.IsFlat g.right] :
    IsIso (sourceIdealMap g) := sorry

/-- The identification `ℐ = f^* 𝒥` of kernel ideals along a strict morphism of first-order
thickenings with `f'` flat. -/
def sourceIdealIso (hg : IsStrict g) [RingedSpace.Hom.IsFlat g.right] :
    (g.left^*).obj (idealModule U.hom) ≅ idealModule T.hom :=
  @asIso _ _ _ _ (sourceIdealMap g) (isIso_sourceIdealMap hg)

/-- The underlying morphism of `sourceIdealIso` is `sourceIdealMap`. -/
theorem sourceIdealIso_hom (hg : IsStrict g) [RingedSpace.Hom.IsFlat g.right] :
    (sourceIdealIso hg).hom = sourceIdealMap g := sorry

/-- Tensoring the identification `ℐ = f^* 𝒥` with an `𝒪_X`-module `F` yields an isomorphism
`f^* 𝒥 ⊗ F ≅ ℐ ⊗ F`. -/
theorem isIso_sourceIdealTensorMap (hg : IsStrict g) [RingedSpace.Hom.IsFlat g.right]
    (F : T.left.Modules) : IsIso (sourceIdealTensorMap g F) := sorry

/-- The identification `f^* 𝒥 ⊗ F ≅ ℐ ⊗ F` obtained by tensoring `sourceIdealIso` with `F`. -/
def sourceIdealTensorIso (hg : IsStrict g) [RingedSpace.Hom.IsFlat g.right]
    (F : T.left.Modules) :
    (g.left^*).obj (idealModule U.hom) ⊗ F ≅ idealModule T.hom ⊗ F :=
  @asIso _ _ _ _ (sourceIdealTensorMap g F) (isIso_sourceIdealTensorMap hg F)

/-- The underlying morphism of `sourceIdealTensorIso` is `sourceIdealTensorMap`. -/
theorem sourceIdealTensorIso_hom (hg : IsStrict g) [RingedSpace.Hom.IsFlat g.right]
    (F : T.left.Modules) :
    (sourceIdealTensorIso hg F).hom = sourceIdealTensorMap g F := sorry

end AlgebraicGeometry.RingedSpace.Thickening.Hom

namespace AlgebraicGeometry.RingedSpace.Modules

open AlgebraicGeometry.RingedSpace.Thickening
open AlgebraicGeometry.RingedSpace.Thickening.Hom

variable {T U : Thickening.{u}} [IsFirstOrderThickening T.hom] [IsFirstOrderThickening U.hom]

/-- The relative identity infinitesimal comparison `c = 1` of Lemma 91.4.4 after identifying
`ℐ` with `f^* 𝒥`, as the pushforward-level map whose restriction is
`(sourceIdealTensorIso hg F).inv`. -/
def relativeIdentityInfinitesimalMap (g : T ⟶ U) (hg : IsStrict g)
    [RingedSpace.Hom.IsFlat g.right] (F : T.left.Modules) :
    kernelIdealSheaf T.hom ⊗ (T.hom _*).obj F ⟶
      (T.hom _*).obj ((g.left^*).obj (idealModule U.hom) ⊗ F) :=
  infinitesimalMap_ofRestrict T.hom (sourceIdealTensorIso hg F).inv

/-- Restricting the relative identity infinitesimal comparison recovers the inverse of
`sourceIdealTensorMap`. -/
theorem relativeIdentityInfinitesimalMap_restrict (g : T ⟶ U) (hg : IsStrict g)
    [RingedSpace.Hom.IsFlat g.right] (F : T.left.Modules) :
    infinitesimalMap_restrict T.hom (relativeIdentityInfinitesimalMap g hg F) =
      (sourceIdealTensorIso hg F).inv := sorry

end AlgebraicGeometry.RingedSpace.Modules

namespace AlgebraicGeometry.RingedSpace.Thickening.Hom.FlatLift

open AlgebraicGeometry.RingedSpace.Modules

variable {T U : Thickening.{u}} [IsFirstOrderThickening T.hom] [IsFirstOrderThickening U.hom]
variable {g : T ⟶ U} {F : T.left.Modules}

/-- The 08L4 extension with coefficients `f^* 𝒥 ⊗ F` and infinitesimal map `c = 1` associated
to a flat lift `(F', α)`, obtained by transporting `toInfinitesimalExtension` along
`sourceIdealTensorIso`. -/
def toRelativeInfinitesimalExtension (hg : IsStrict g)
    [SheafOfModules.IsFlatOver F g.left] [RingedSpace.Hom.IsFlat g.right]
    (L : FlatLift g F) :
    InfinitesimalExtension T.hom F ((g.left^*).obj (idealModule U.hom) ⊗ F)
      (relativeIdentityInfinitesimalMap g hg F) where
  module := L.module
  ι := (T.hom _*).map (sourceIdealTensorIso hg F).hom ≫ (toInfinitesimalExtension hg L).ι
  π := (toInfinitesimalExtension hg L).π
  w := sorry
  shortExact := sorry
  infMap_eq := sorry

/-- The middle `𝒪_{X'}`-module of the relative 08L4 extension is the lifted module. -/
theorem toRelativeInfinitesimalExtension_module (hg : IsStrict g)
    [SheafOfModules.IsFlatOver F g.left] [RingedSpace.Hom.IsFlat g.right]
    (L : FlatLift g F) :
    (toRelativeInfinitesimalExtension hg L).module = L.module := sorry

/-- The projection of the relative 08L4 extension is the adjunct of `α`. -/
theorem toRelativeInfinitesimalExtension_π (hg : IsStrict g)
    [SheafOfModules.IsFlatOver F g.left] [RingedSpace.Hom.IsFlat g.right]
    (L : FlatLift g F) :
    (toRelativeInfinitesimalExtension hg L).π = (toInfinitesimalExtension hg L).π := sorry

/-- The braiding `f^* 𝒥 ⊗ F ≅ F ⊗ f^* 𝒥` of `𝒪_X`-modules. -/
def sourceIdealBraid (F : T.left.Modules) :
    (g.left^*).obj (idealModule U.hom) ⊗ F ≅
      F ⊗ (g.left^*).obj (idealModule U.hom) :=
  β_ ((g.left^*).obj (idealModule U.hom)) F

/-- The underlying morphism of `sourceIdealBraid` is the braiding `β_`. -/
theorem sourceIdealBraid_hom (F : T.left.Modules) :
    (sourceIdealBraid F).hom =
      (β_ ((g.left^*).obj (idealModule U.hom)) F).hom := sorry

/-- Along a strict morphism of first-order thickenings, the comparison
`f^* 𝒥 ⊗ i^* F' ⟶ ℐ F'` attached to a flat lift is an isomorphism. -/
theorem isIso_sourceIdealMulMap (hg : IsStrict g) (L : FlatLift g F) :
    IsIso (sourceIdealMulMap g L.module) := sorry

end AlgebraicGeometry.RingedSpace.Thickening.Hom.FlatLift
