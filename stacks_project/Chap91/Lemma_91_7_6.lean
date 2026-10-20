/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap91.Lemma_91_7_1_Diagram
public import stacks_project.Chap91.Lemma_91_7_4
public import stacks_project.Chap91.Lemma_91_7_6_Map
import Mathlib.Tactic.CrossRefAttribute

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

/-- The identity-base connecting diagram of two square-zero `f⁻¹ 𝒪_S`-algebra
extensions, with vertical map `g` and `ν` the adjunct of `c` transported along
the kernel identifications. -/
def ofIdentityBase (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F))
    (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G)) :
    RelativeDiagram SY.i (g ≫ f) SY.f' (𝟙 S) SX.i f SX.f' (𝟙 S) g (𝟙 S) (𝟙 S) where
  comm := CommDiagram.mk SY.commutes SX.commutes (Category.comp_id (g ≫ f)) rfl
  ν :=
    SX.kernelIso.hom ≫ (pullbackPushforwardAdjunction g).homEquiv F G c ≫
      (g _*).map SY.kernelIso.inv
  comm_kernel := sorry

/-- `ofIdentityBase` has identity maps on `S`, vertical map `g`, and `ν` the
adjunct of `c` transported along `kernelIso`. -/
theorem ofIdentityBase_spec (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F))
    (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G)) :
    (ofIdentityBase c SX SY).comm.back.w = SY.commutes ∧
      (ofIdentityBase c SX SY).comm.front.w = SX.commutes ∧
      (ofIdentityBase c SX SY).ν =
        SX.kernelIso.hom ≫ (pullbackPushforwardAdjunction g).homEquiv F G c ≫
          (g _*).map SY.kernelIso.inv := sorry

end RelativeDiagram

namespace Solution

/-- Lemma 91.7.6 Let f : (X, 𝒪_X) ⟶ (S, 𝒪_S) and g : (Y, 𝒪_Y) ⟶ (X, 𝒪_X) be
morphisms of ringed spaces. Let F be an 𝒪_X-module, G an 𝒪_Y-module, and
c : (g^*).obj F ⟶ G an 𝒪_Y-linear g-map. Let 0 ⟶ F ⟶ 𝒪_{X'} ⟶ 𝒪_X ⟶ 0 be an
extension of f⁻¹ 𝒪_S-algebras corresponding to
ξ = (extensionEquiv f F).symm (isoClassMk SX), and
0 ⟶ G ⟶ 𝒪_{Y'} ⟶ 𝒪_Y ⟶ 0 an extension of g⁻¹ f⁻¹ 𝒪_S-algebras corresponding
to ζ = (extensionEquiv (g ≫ f) G).symm (isoClassMk SY). Then there is an
S-morphism g' : Y' ⟶ X' compatible with g and c if and only if extOne_map c ξ
equals extOne_comap f g ζ in Ext⁽1⁾(L(g)^* NL[f], G). -/
@[stacks 0GQ1]
theorem fittingMap_nonempty_iff (c : (g^*).obj F ⟶ G)
    (SX : Solution (𝟙 S) f F (zeroKernelMap f F))
    (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G)) :
    Nonempty (FittingMap (RelativeDiagram.ofIdentityBase c SX SY)) ↔
      extOne_map c ((extensionEquiv f F).symm (isoClassMk SX)) =
        extOne_comap f g ((extensionEquiv (g ≫ f) G).symm (isoClassMk SY)) :=
  sorry

end Solution

end AlgebraicGeometry.RingedSpace.Thickening
