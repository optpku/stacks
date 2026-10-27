/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.FlatLift.Classification
public import stacks_project.Chap91.Lemma_91_7_1_Obstruction
import StacksCheckRecall

/-!
# Principal homogeneous space of flat first-order deformations of schemes

If `S ⊂ S'` is a first-order thickening of schemes and `f : X ⟶ S` is flat,
and there exists a flat `f' : X' ⟶ S'` with an `S`-isomorphism
`a : X ≅ X' ×_{S'} S`, then isomorphism classes of such pairs are principal
homogeneous under Ext¹_{𝒪_X}(NL[X/S], f^* 𝒞_{S/S'}), and automorphisms of a
given `X'` over `S'` reducing to the identity on `X' ×_{S'} S` are
Ext⁰_{𝒪_X}(NL[X/S], f^* 𝒞_{S/S'}).
-/

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 91.8.1 (1). For a first-order thickening and a flat morphism admitting a flat
lift with specified closed fibre, its lift classes form a principal homogeneous space
under Ext¹ of the naive cotangent complex against the pulled conormal module. -/
@[stacks 0D14] #check (AlgebraicGeometry.Scheme.Thickening.FlatLift.addTorsor :
  ∀ {S S' X : Scheme.{u}} {t : S ⟶ S'} [IsFirstOrderThickening t]
    {f : X ⟶ S} [Flat f],
    AlgebraicGeometry.Scheme.Thickening.FlatLift t f →
      AddTorsor (AlgebraicGeometry.Scheme.Thickening.extOneNL t f)
        (AlgebraicGeometry.Scheme.Thickening.FlatLift.IsoClass t f))

#check (AlgebraicGeometry.Scheme.Thickening.FlatLift.isoClassEquiv :
  ∀ {S S' X : Scheme.{u}} {t : S ⟶ S'} [IsFirstOrderThickening t]
    {f : X ⟶ S} [Flat f],
    AlgebraicGeometry.Scheme.Thickening.FlatLift t f →
      (AlgebraicGeometry.Scheme.Thickening.extOneNL t f ≃
        AlgebraicGeometry.Scheme.Thickening.FlatLift.IsoClass t f))

/- Lemma 91.8.1 (2). Automorphisms of a flat lift over the thickened base that induce
the identity on the specified closed fibre are classified by Ext⁰ of the naive
cotangent complex against the pulled conormal module. -/
@[stacks 0D14] #check (AlgebraicGeometry.Scheme.Thickening.FlatLift.reduceIdAutoEquiv :
  ∀ {S S' X : Scheme.{u}} {t : S ⟶ S'} [IsFirstOrderThickening t]
    {f : X ⟶ S} [Flat f] (L : AlgebraicGeometry.Scheme.Thickening.FlatLift t f),
    AlgebraicGeometry.Scheme.Thickening.FlatLift.ReduceIdAuto L ≃
      AlgebraicGeometry.Scheme.Thickening.extZeroNL t f)
