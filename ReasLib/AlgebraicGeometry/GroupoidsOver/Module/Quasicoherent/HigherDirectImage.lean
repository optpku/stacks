/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Pushforward
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Coreflector
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.FlatBaseChange.DirectImage
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation

/-! # Quasi-coherent higher direct images of algebraic stacks

The explicit small-section and injective-resolution certificates implement the
size convention for derived images in the original coefficient universe.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- Restriction of `R^i f_*` of a quasi-coherent module lies in étale
`LQCoh^{fbc}`. -/
theorem qCohHigherDirectImage_mem_lqcohFbc {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    [HasSmallAssociatedTypeSections f StandardTopology.fppf]
    [resolutions : HasInjectiveResolutions (AlgebraicStack.fppfModules X)]
    (i : ℕ) (F : QCoh X) :
    lqcohFbc Y
      ((QCoh.inclusion X ⋙
          AlgebraicStack.fppfHigherDirectImageFunctor f i ⋙
          restriction Y).obj F) :=
  sorry

/-- The degree-`i` quasi-coherent higher direct image functor
`R^i f_{QCoh,*} : QCoh 𝒳 ⥤ QCoh 𝒴`, obtained by lifting the restriction of
`AlgebraicStack.fppfHigherDirectImageFunctor f i` into `LQCoh^{fbc} 𝒴`
and applying `LQCohFbc.toQCoh`. -/
def qCohHigherDirectImageFunctor {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    [HasSmallAssociatedTypeSections f StandardTopology.fppf]
    [resolutions : HasInjectiveResolutions (AlgebraicStack.fppfModules X)] (i : ℕ) :
    QCoh X ⥤ QCoh Y :=
  (lqcohFbc Y).lift
      (QCoh.inclusion X ⋙
        @Functor.rightDerived _ _ _ _ _ resolutions _
          (AlgebraicStack.fppfModulePushforward f)
          (AlgebraicStack.fppfModulePushforward_additive f) i ⋙ restriction Y)
      (qCohHigherDirectImage_mem_lqcohFbc f i) ⋙
    LQCohFbc.toQCoh Y

/-- The degree-`i` quasi-coherent higher direct image `R^i f_{QCoh,*} F`. -/
def qCohHigherDirectImage {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    [HasSmallAssociatedTypeSections f StandardTopology.fppf]
    [resolutions : HasInjectiveResolutions (AlgebraicStack.fppfModules X)]
    (F : QCoh X) (i : ℕ) : QCoh Y :=
  (qCohHigherDirectImageFunctor f i).obj F

/-- Quasi-coherent higher direct images are additive. -/
instance qCohHigherDirectImageFunctor_additive {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    [HasSmallAssociatedTypeSections f StandardTopology.fppf]
    [HasInjectiveResolutions (AlgebraicStack.fppfModules X)] (i : ℕ) :
    (qCohHigherDirectImageFunctor f i).Additive := sorry

namespace QCoh

/-- The quasi-coherent higher direct image functor, with explicit original-universe
size and resolution conventions, is the canonical fppf-derived construction. -/
abbrev higherDirectImageFunctor {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    [HasSmallAssociatedTypeSections f StandardTopology.fppf]
    [HasInjectiveResolutions (AlgebraicStack.fppfModules X)] (i : ℕ) :
    QCoh X ⥤ QCoh Y := qCohHigherDirectImageFunctor f i

/-- The quasi-coherent higher direct image of a module is its canonical
fppf-derived higher direct image in the supplied size and resolution convention. -/
abbrev higherDirectImage {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    [HasSmallAssociatedTypeSections f StandardTopology.fppf]
    [HasInjectiveResolutions (AlgebraicStack.fppfModules X)]
    (F : QCoh X) (i : ℕ) : QCoh Y := qCohHigherDirectImage f F i

/-- Fppf realization of the étale restriction of a quasi-coherent module
recovers its original fppf module sheaf. -/
theorem toLQCohFbc_comp_toFppf (X : GroupoidsOver S) [AlgebraicStack X] :
    Nonempty (toLQCohFbc X ⋙ LQCohFbc.toFppf X ≅ inclusion X) := sorry

/-- Quasi-coherent higher direct image also has the presentation by inclusion
into flat-base-change modules, higher direct image there, and the coreflector. -/
theorem higherDirectImageFunctor_iso_lqcoh {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    [HasSmallAssociatedTypeSections f StandardTopology.fppf]
    [HasInjectiveResolutions (AlgebraicStack.fppfModules X)] (i : ℕ) :
    Nonempty (higherDirectImageFunctor f i ≅
      toLQCohFbc X ⋙ LQCohFbc.higherDirectImageFunctor f i ⋙ LQCohFbc.toQCoh Y) := sorry

end QCoh

/-- `qCohHigherDirectImageFunctor` is the lift of restricted derived module
pushforward, followed by `Q`. -/
theorem qCohHigherDirectImageFunctor_eq {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    [HasSmallAssociatedTypeSections f StandardTopology.fppf]
    [resolutions : HasInjectiveResolutions (AlgebraicStack.fppfModules X)] (i : ℕ) :
    qCohHigherDirectImageFunctor f i =
      (lqcohFbc Y).lift
          (QCoh.inclusion X ⋙
            AlgebraicStack.fppfHigherDirectImageFunctor f i ⋙ restriction Y)
          (qCohHigherDirectImage_mem_lqcohFbc f i) ⋙
        LQCohFbc.toQCoh Y :=
  rfl

/-- `qCohHigherDirectImage f F i` is the object map of
`qCohHigherDirectImageFunctor f i`. -/
theorem qCohHigherDirectImage_eq {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    [HasSmallAssociatedTypeSections f StandardTopology.fppf]
    [resolutions : HasInjectiveResolutions (AlgebraicStack.fppfModules X)]
    (F : QCoh X) (i : ℕ) :
    qCohHigherDirectImage f F i = (qCohHigherDirectImageFunctor f i).obj F :=
  rfl

end AlgebraicGeometry.GroupoidsOver
