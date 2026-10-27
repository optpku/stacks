/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.Solution.Pushout
public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.Solution.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.NaiveCotangent.InverseImage.Ext
public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.Solution.Functoriality

/-! # Pushout, pullback, and classification of square-zero extensions -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open AlgebraicGeometry AlgebraicGeometry.RingedSpace AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Thickening
open SheafOfModules.RingedSite
open TopologicalSpace Opposite
open scoped AlgebraicGeometry DerivedExt RingedSpaceDerivedPullback

noncomputable section

universe u

open AlgebraicGeometry.RingedSpace.NaiveCotangent.InverseImage

namespace AlgebraicGeometry.RingedSpace.Thickening.Solution

variable {S X Y : RingedSpace.{u}}
variable {f : X ⟶ S} {g : Y ⟶ X}
variable {F : X.Modules} {G : Y.Modules}

/-- A compatible morphism of relative square-zero extensions exists exactly when coefficient pushout and algebra pullback have the same extension class. -/
theorem exists_fittingMap_iff_isoClass (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F))
    (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G)) :
    Nonempty (IdentityBaseFitting c SX SY) ↔
      isoClassMk (pushoutAlong g c SX) = isoClassMk (pullbackAlong g SY) := sorry

/-- The class of a coefficient pushout is the image of the original extension class under derived pullback and the coefficient map. -/
theorem pushoutAlong_extClass (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F)) :
    extOne_inverseImageIso f g G
        ((extensionEquiv (inverseImageTo g ≫ f) (restrictToInverseImage g G)).symm
          (isoClassMk (pushoutAlong g c SX))) =
      extOne_map c ((extensionEquiv f F).symm (isoClassMk SX)) := sorry

/-- The class of an algebra pullback is the image of the original extension class under the naive-cotangent comparison. -/
theorem pullbackAlong_extClass
    (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G)) :
    extOne_inverseImageIso f g G
        ((extensionEquiv (inverseImageTo g ≫ f) (restrictToInverseImage g G)).symm
          (isoClassMk (pullbackAlong g SY))) =
      extOne_comap f g ((extensionEquiv (g ≫ f) G).symm (isoClassMk SY)) := sorry

end AlgebraicGeometry.RingedSpace.Thickening.Solution
