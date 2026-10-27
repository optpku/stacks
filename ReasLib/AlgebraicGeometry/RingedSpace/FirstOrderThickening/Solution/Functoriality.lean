/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.NaiveCotangent.Ext
public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.Solution.AlgebraExtension
public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.FittingMap

/-!
# Functoriality of square-zero f⁻¹𝒪_S-algebra extensions of ringed spaces

A morphism of ringed spaces over `(S, 𝒪_S)` compatible with `g` and a
coefficient map `c : g^* F ⟶ G` exists if and only if the Ext¹ classes of
the two identity-base extensions agree in `Ext⁽1⁾(L(g)^* NL[f], G)`.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Thickening
open AlgebraicGeometry.RingedSpace.Thickening.Solution
open scoped AlgebraicGeometry DerivedExt RingedSpaceDerivedPullback

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Thickening

variable {S X Y : RingedSpace.{u}}
variable {f : X ⟶ S} {g : Y ⟶ X}
variable {F : X.Modules} {G : Y.Modules}

namespace RelativeDiagram

/-- The identity-base comparison respects the transported coefficient map. -/
private theorem ofIdentityBase_kernelSquare (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F))
    (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G)) :
    @KernelSquare _ _ _ _ _ _ _ _
      SY.i (g ≫ f) SY.f' (𝟙 S) SX.i f SX.f' (𝟙 S) g (𝟙 S) (𝟙 S)
      SY.i_isFirstOrder inferInstance SX.i_isFirstOrder inferInstance
      (@CommDiagram.mk _ _ _ _ _ _ _ _
      SY.i (g ≫ f) SY.f' (𝟙 S) SX.i f SX.f' (𝟙 S) g (𝟙 S) (𝟙 S)
      SY.i_isFirstOrder inferInstance SX.i_isFirstOrder inferInstance SY.commutes SX.commutes (Category.comp_id (g ≫ f)) rfl)
      (SX.kernelIso.hom ≫ (pullbackPushforwardAdjunction g).homEquiv F G c ≫
      (g _*).map SY.kernelIso.inv) := sorry

/-- The identity-base connecting diagram of two square-zero `f⁻¹ 𝒪_S`-algebra
extensions, with vertical map `g` and `ν` the adjunct of `c` transported along
the kernel identifications. -/
@[no_expose] def ofIdentityBase (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F))
    (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G)) :
    @RelativeDiagram _ _ _ _ _ _ _ _
      SY.i (g ≫ f) SY.f' (𝟙 S) SX.i f SX.f' (𝟙 S) g (𝟙 S) (𝟙 S)
      SY.i_isFirstOrder inferInstance SX.i_isFirstOrder inferInstance :=
  @RelativeDiagram.of _ _ _ _ _ _ _ _
      SY.i (g ≫ f) SY.f' (𝟙 S) SX.i f SX.f' (𝟙 S) g (𝟙 S) (𝟙 S)
      SY.i_isFirstOrder inferInstance SX.i_isFirstOrder inferInstance
    (@CommDiagram.mk _ _ _ _ _ _ _ _
      SY.i (g ≫ f) SY.f' (𝟙 S) SX.i f SX.f' (𝟙 S) g (𝟙 S) (𝟙 S)
      SY.i_isFirstOrder inferInstance SX.i_isFirstOrder inferInstance SY.commutes SX.commutes (Category.comp_id (g ≫ f)) rfl)
    (
    SX.kernelIso.hom ≫ (pullbackPushforwardAdjunction g).homEquiv F G c ≫
      (g _*).map SY.kernelIso.inv)
    (ofIdentityBase_kernelSquare c SX SY)

/-- `ofIdentityBase` has identity maps on `S`, vertical map `g`, and `ν` the
adjunct of `c` transported along `kernelIso`. -/
theorem ofIdentityBase_spec (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F))
    (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G)) :
    (@CommDiagram.back _ _ _ _ _ _ _ _
      SY.i (g ≫ f) SY.f' (𝟙 S) SX.i f SX.f' (𝟙 S) g (𝟙 S) (𝟙 S)
      SY.i_isFirstOrder inferInstance SX.i_isFirstOrder inferInstance
      (@RelativeDiagram.comm _ _ _ _ _ _ _ _
      SY.i (g ≫ f) SY.f' (𝟙 S) SX.i f SX.f' (𝟙 S) g (𝟙 S) (𝟙 S)
      SY.i_isFirstOrder inferInstance SX.i_isFirstOrder inferInstance (ofIdentityBase c SX SY))).w = SY.commutes ∧
      (@CommDiagram.front _ _ _ _ _ _ _ _
      SY.i (g ≫ f) SY.f' (𝟙 S) SX.i f SX.f' (𝟙 S) g (𝟙 S) (𝟙 S)
      SY.i_isFirstOrder inferInstance SX.i_isFirstOrder inferInstance
      (@RelativeDiagram.comm _ _ _ _ _ _ _ _
      SY.i (g ≫ f) SY.f' (𝟙 S) SX.i f SX.f' (𝟙 S) g (𝟙 S) (𝟙 S)
      SY.i_isFirstOrder inferInstance SX.i_isFirstOrder inferInstance (ofIdentityBase c SX SY))).w = SX.commutes ∧
      (@RelativeDiagram.ν _ _ _ _ _ _ _ _
      SY.i (g ≫ f) SY.f' (𝟙 S) SX.i f SX.f' (𝟙 S) g (𝟙 S) (𝟙 S)
      SY.i_isFirstOrder inferInstance SX.i_isFirstOrder inferInstance (ofIdentityBase c SX SY)) =
        SX.kernelIso.hom ≫ (pullbackPushforwardAdjunction g).homEquiv F G c ≫
          (g _*).map SY.kernelIso.inv := sorry

end RelativeDiagram

namespace Solution

/-- Compatible identity-base fillings use the certificates stored in both solutions. -/
abbrev IdentityBaseFitting (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F))
    (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G)) :=
  @FittingMap _ _ _ _ _ _ _ _
      SY.i (g ≫ f) SY.f' (𝟙 S) SX.i f SX.f' (𝟙 S) g (𝟙 S) (𝟙 S)
      SY.i_isFirstOrder inferInstance SX.i_isFirstOrder inferInstance (RelativeDiagram.ofIdentityBase c SX SY)

/-- Two relative square-zero algebra extensions admit a morphism inducing the prescribed
base and coefficient maps if and only if their canonical Ext¹ classes have equal images
under derived pullback with coefficient transport and naive-cotangent precomposition. -/
theorem fittingMap_nonempty_iff (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F))
    (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G)) :
    Nonempty (IdentityBaseFitting c SX SY) ↔
      extOne_map c ((extensionEquiv f F).symm (isoClassMk SX)) =
        extOne_comap f g ((extensionEquiv (g ≫ f) G).symm (isoClassMk SY)) := sorry

end Solution

end AlgebraicGeometry.RingedSpace.Thickening
