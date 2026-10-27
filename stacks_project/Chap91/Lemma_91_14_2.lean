/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.FlatLift.IsoClass
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.FlatLift.Automorphisms
import StacksCheckRecall

public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Thickening

universe u

/- Lemma 91.14.2 (1). For a flat morphism `f : X ⟶ Y` across a first-order
thickening `t : Y ⟶ Y'` over a scheme `S`, a flat lift supplies an Ext¹ torsor
of isomorphism classes of flat lifts, with coefficients `f^* 𝒞_{Y/Y'}`. -/
@[stacks 0D17] #check
  (AlgebraicGeometry.AlgebraicSpace.Thickening.FlatLift.addTorsor :
    {S : Scheme.{u}} → {Y Y' X : AlgebraicSpace S} →
    {t : Y ⟶ Y'} → [IsFirstOrderThickening t] → {f : X ⟶ Y} → [Flat f] →
    FlatLift t f → AddTorsor (extOneNL t f) (FlatLift.IsoClass t f))

/- Lemma 91.14.2 (2). Automorphisms of a flat lift over `Y'` restricting to the
identity on its closed fibre `X` correspond to Ext⁰ of `NL[f]` with
coefficients `f^* 𝒞_{Y/Y'}`. -/
@[stacks 0D17] #check
  (AlgebraicGeometry.AlgebraicSpace.Thickening.FlatLift.reduceIdAutoEquiv :
    {S : Scheme.{u}} → {Y Y' X : AlgebraicSpace S} →
    {t : Y ⟶ Y'} → [IsFirstOrderThickening t] → {f : X ⟶ Y} → [Flat f] →
    (L : FlatLift t f) → FlatLift.ReduceIdAuto L ≃ extZeroNL t f)
