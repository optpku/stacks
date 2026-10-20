/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FieldFiber.Point
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.Fiberwise
import StacksCheckRecall

/-!
# Fibrewise relative flatness at a point of an algebraic space

In a commutative triangle of algebraic spaces, relative flatness of a quasi-coherent module
along the fibre of `X ⟶ Z` over the fibre of `Y ⟶ Z` at a point of `|X|` may be tested on
étale stalks, on the field-valued fibre product, or on an étale scheme presentation.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

/- Lemma 76.23.1: let `S` be a scheme and let `f : X ⟶ Y`, `h : Y ⟶ Z` be morphisms of
algebraic spaces over `S`. Let `F` be a quasi-coherent `𝒪_X`-module and let `x ∈ |X|`. The
following are equivalent. (1) For a geometric point `xbar` of `X` over `x`, writing
`ȳ = xbar.map f` and `z̄ = ȳ.map h`, the module `F_{x̄} / m_{z̄} F_{x̄}` is flat over
`𝒪_{Y, ȳ} / m_{z̄} 𝒪_{Y, ȳ}`. (2) For a morphism `Spec(K) ⟶ X` in the class of `x`, writing
`z` for its composite to `Z`, `X_z = Spec(K) ×_Z X`, `Y_z = Spec(K) ×_Z Y`, and `F_z` the
pullback of `F` to `X_z`, the sheaf `F_z` is flat at `x` over `Y_z`. (3) For schemes `U, V, W`
étale over `X, Y, Z` fitting in a commutative diagram, and a point `u ∈ U` mapping to `x` with
image `w ∈ W`, the pullback of `F` to the fibre `U_w` is flat over `V_w` at `u`. -/
@[stacks 05WY] #check (AlgebraicGeometry.AlgebraicSpace.Modules.flatOnFiberAt_tfae :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
      (F : X.Modules) [F.IsQuasicoherent] (f : X ⟶ Y) (h : Y ⟶ Z)
      (x : Points X) (xbar : GeometricPoint X), xbar.liesOver x →
      ∀ (p : FieldValuedPoint X), Points.mk p = x →
      ∀ (U V W : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (c : ofOver W ⟶ Z)
        (toV : U ⟶ V) (toW : V ⟶ W) [Etale a] [Etale b] [Etale c] (u : U.left),
        a ≫ f = ofOverMap toV ≫ b →
        b ≫ h = ofOverMap toW ≫ c →
        Points.map a (ofOver.pointsEquiv U u) = x →
        List.TFAE [stalkFiberFlatAlong F f h xbar, fieldFiberFlatOverAt F f h p,
          etaleFiberFlatOverAt F a toV toW u])
