/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Modules.InfinitesimalExtension.ExtPushout
import StacksCheckRecall

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.Abelian (Ext)
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.IsFirstOrderThickening
open AlgebraicGeometry.RingedSpace.Modules
open AlgebraicGeometry.RingedSpace.Modules.InfinitesimalExtension
open scoped AlgebraicGeometry

universe u

/- Remark 91.4.8 Let `(X, 𝒪_X)`, first-order thickenings
`(X, 𝒪_X) ⟶ (X'_i, 𝒪_{X'_i})`, and `h : (X'_1, 𝒪_{X'_1}) ⟶ (X'_2, 𝒪_{X'_2})`
be as in Remark 91.4.7. Given trivializations `π_i` with
`π_1 = h ≫ π_2`, `𝒪_X`-modules `ℱ`, `𝒦_i`, maps `c_i`, and
`κ : 𝒦_2 ⟶ 𝒦_1` making the `c`-square commute, the construction of
Remark 91.4.6 yields a commutative square whose left vertical is the 08L4
pushout of Remark 91.4.7, whose horizontals send an 08L4 isomorphism class
to its `Ext ℱ 𝒦_i 1` class, and whose right vertical is `Ext` postcomposition
along `κ`. -/
@[stacks 08LD] #check
  (AlgebraicGeometry.RingedSpace.Modules.InfinitesimalExtension.extClassOnIsoClass_pushout :
    ∀ {X X1 X2 : RingedSpace.{u}} {i1 : X ⟶ X1} [IsFirstOrderThickening i1]
      {h : X1 ⟶ X2} [IsFirstOrderThickening (i1 ≫ h)]
      (τ1 : Trivialization i1) (τ2 : Trivialization (i1 ≫ h))
      [HasExt.{u} X.Modules] {F K1 K2 : X.Modules}
      (c1 : kernelIdealSheaf i1 ⊗ (i1 _*).obj F ⟶ (i1 _*).obj K1)
      {c2 : kernelIdealSheaf (i1 ≫ h) ⊗ ((i1 ≫ h) _*).obj F ⟶ ((i1 ≫ h) _*).obj K2}
      (κ : K2 ⟶ K1) (hc : infinitesimalMapCommSq c1 c2 κ)
      (retraction_comm : h ≫ τ2.retraction = τ1.retraction)
      (p : IsoClass (i1 ≫ h) F K2 c2),
      extClassOnIsoClass τ1 c1 (pushoutOnIsoClass c1 κ hc p) =
        (Ext.mk₀ κ).postcomp F (add_zero 1) (extClassOnIsoClass τ2 c2 p))
