/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap91.Lemma_91_7_1_Diagram
public import stacks_project.Chap91.Lemma_91_7_4
public import stacks_project.Chap91.Lemma_91_7_6_Map
public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.Solution.Functoriality
import StacksCheckRecall

/-!
# Functoriality of square-zero f⁻¹𝒪_S-algebra extensions of ringed spaces

A morphism of ringed spaces over `(S, 𝒪_S)` compatible with `g` and a
coefficient map `c : g^* F ⟶ G` exists if and only if the Ext¹ classes of
the two identity-base extensions agree in `Ext⁽1⁾(L(g)^* NL[f], G)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Thickening
open AlgebraicGeometry.RingedSpace.Thickening.Solution
open scoped AlgebraicGeometry DerivedExt RingedSpaceDerivedPullback

noncomputable section

universe u

/- Lemma 91.7.6 Let f : (X, 𝒪_X) ⟶ (S, 𝒪_S) and g : (Y, 𝒪_Y) ⟶ (X, 𝒪_X) be
morphisms of ringed spaces. Let F be an 𝒪_X-module, G an 𝒪_Y-module, and
c : (g^*).obj F ⟶ G an 𝒪_Y-linear g-map. Let 0 ⟶ F ⟶ 𝒪_{X'} ⟶ 𝒪_X ⟶ 0 be an
extension of f⁻¹ 𝒪_S-algebras corresponding to
ξ = (extensionEquiv f F).symm (isoClassMk SX), and
0 ⟶ G ⟶ 𝒪_{Y'} ⟶ 𝒪_Y ⟶ 0 an extension of g⁻¹ f⁻¹ 𝒪_S-algebras corresponding
to ζ = (extensionEquiv (g ≫ f) G).symm (isoClassMk SY). Then there is an
S-morphism g' : Y' ⟶ X' compatible with g and c if and only if extOne_map c ξ
equals extOne_comap f g ζ in Ext⁽1⁾(L(g)^* NL[f], G). -/
@[stacks 0GQ1] #check
  (AlgebraicGeometry.RingedSpace.Thickening.Solution.fittingMap_nonempty_iff :
    ∀ {S X Y : RingedSpace.{u}} {f : X ⟶ S} {g : Y ⟶ X}
      {F : X.Modules} {G : Y.Modules} (c : (g^*).obj F ⟶ G)
      (SX : Solution (𝟙 S) f F (zeroKernelMap f F))
      (SY : Solution (𝟙 S) (g ≫ f) G (zeroKernelMap (g ≫ f) G)),
      Nonempty (IdentityBaseFitting c SX SY) ↔
        extOne_map c ((extensionEquiv f F).symm (isoClassMk SX)) =
          extOne_comap f g ((extensionEquiv (g ≫ f) G).symm (isoClassMk SY)))
