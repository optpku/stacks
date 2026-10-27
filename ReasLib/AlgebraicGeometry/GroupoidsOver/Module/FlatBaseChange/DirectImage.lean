/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.FlatBaseChange.Fppf
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.DirectImage
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.HigherDirectImage
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Modules
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation

/-! # Direct images of locally quasi-coherent modules with flat base change

Small-section and injective-resolution certificates express the size convention
for the module categories. Derived smallness is supplied independently of
underived compatible-section smallness.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty
open scoped Bicategory

noncomputable section
universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

namespace LQCohFbc

/-- Étale direct image along a quasi-compact quasi-separated morphism
preserves local quasi-coherence and flat base change. The small-section
certificate implements the size convention for the original module universe. -/
theorem mem_directImage {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    [HasSmallCFGTypeSections f] (F : LQCohFbc X) :
    lqcohFbc Y ((etaleModuleDirectImage f).obj ((inclusion X).obj F)) := sorry

/-- Direct image on locally quasi-coherent modules with flat base change,
formed using the supplied compatible-section size convention. -/
def directImage {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    [HasSmallCFGTypeSections f] : LQCohFbc X ⥤ LQCohFbc Y :=
  (lqcohFbc Y).lift (inclusion X ⋙ etaleModuleDirectImage f) (mem_directImage f)

/-- Forgetting the flat-base-change condition recovers étale direct image. -/
theorem directImage_comp_inclusion {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    [HasSmallCFGTypeSections f] :
    directImage f ⋙ inclusion Y = inclusion X ⋙ etaleModuleDirectImage f := rfl

/-- Direct image on locally quasi-coherent modules with flat base change is additive. -/
instance directImage_additive {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    [HasSmallCFGTypeSections f] : (directImage f).Additive := sorry

/-- Fppf higher direct image followed by étale restriction preserves local
quasi-coherence and flat base change, under the supplied size and resolution
certificates for the original coefficient universe. -/
theorem mem_higherDirectImage {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    [HasSmallAssociatedTypeSections f StandardTopology.fppf]
    [HasInjectiveResolutions (AlgebraicStack.fppfModules X)]
    (i : ℕ) (F : LQCohFbc X) :
    lqcohFbc Y ((toFppf X ⋙ AlgebraicStack.fppfHigherDirectImageFunctor f i ⋙
      restriction Y).obj F) := sorry

/-- Higher direct image on locally quasi-coherent modules with flat base
change is computed on their actual fppf realization. The size and resolution
certificates implement the original-universe size convention. -/
def higherDirectImageFunctor {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    [HasSmallAssociatedTypeSections f StandardTopology.fppf]
    [resolutions : HasInjectiveResolutions (AlgebraicStack.fppfModules X)]
    (i : ℕ) : LQCohFbc X ⥤ LQCohFbc Y :=
  (lqcohFbc Y).lift
    (toFppf X ⋙
      @Functor.rightDerived _ _ _ _ _ resolutions _
        (AlgebraicStack.fppfModulePushforward f)
        (AlgebraicStack.fppfModulePushforward_additive f) i ⋙ restriction Y)
    (mem_higherDirectImage f i)

/-- After the canonical coefficient lift, fppf-computed higher direct image
agrees with enlarged-coefficient étale higher direct image. -/
theorem higherDirectImageFunctor_comp_lift {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    [HasSmallAssociatedTypeSections f StandardTopology.fppf]
    [HasInjectiveResolutions (AlgebraicStack.fppfModules X)] (i : ℕ) :
    Nonempty (higherDirectImageFunctor f i ⋙ inclusion Y ⋙ ModuleUniverseComparison.lift Y ≅
      inclusion X ⋙ moduleHigherDirectImageFunctor f i) := sorry

/-- Higher direct images on locally quasi-coherent modules with flat base
change are additive. -/
instance higherDirectImageFunctor_additive {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    [HasSmallAssociatedTypeSections f StandardTopology.fppf]
    [HasInjectiveResolutions (AlgebraicStack.fppfModules X)] (i : ℕ) :
    (higherDirectImageFunctor f i).Additive := sorry

end LQCohFbc
end AlgebraicGeometry.GroupoidsOver
