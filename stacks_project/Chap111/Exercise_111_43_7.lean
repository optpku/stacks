/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AffineTriangle.Picard
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Cohomology
import StacksCheckRecall

/-!
# Exercise 111.43.7

The affine triangle is an affine scheme with nontrivial Picard group, so
Zariski `H¹(X, -)` on abelian sheaves is not the zero functor.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

noncomputable section

/- Exercise 111.43.7 (1): the rational affine triangle is an affine scheme with
nontrivial Picard group. -/
@[stacks 0DAQ] #check
  (AlgebraicGeometry.AffineTriangle.rational_isAffine_nontrivial_picardGroup :
    IsAffine (AlgebraicGeometry.AffineTriangle.scheme ℚ) ∧
      Nontrivial (AlgebraicGeometry.AffineTriangle.scheme ℚ).PicardGroup)

/- Exercise 111.43.7 (2): degree-one cohomology on abelian sheaves is not the zero
functor for any scheme with nontrivial Picard group. -/
@[stacks 0DAQ] #check
  (AlgebraicGeometry.Scheme.functorH_one_not_isZero : ∀ {X : Scheme.{u}}
    [HasSheafify (Opens.grothendieckTopology X.toRingedSpace) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.toRingedSpace) AddCommGrpCat.{u})]
    [Nontrivial X.PicardGroup],
    ¬ IsZero (Sheaf.functorH (Opens.grothendieckTopology X.toRingedSpace) 1))

#check
  (AlgebraicGeometry.AffineTriangle.nontrivial_picardGroup :
    ∀ (k : Type u) [Field k] [Nontrivial kˣ],
      Nontrivial (AlgebraicGeometry.AffineTriangle.scheme k).PicardGroup)

#check
  (AlgebraicGeometry.Scheme.unitsAddSheaf_functorH_one_not_isZero : ∀ {X : Scheme.{u}}
    [HasSheafify (Opens.grothendieckTopology X.toRingedSpace) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.toRingedSpace) AddCommGrpCat.{u})]
    [Nontrivial X.PicardGroup],
    ¬ IsZero
        ((Sheaf.functorH (Opens.grothendieckTopology X.toRingedSpace) 1).obj
          (Sheaf.unitsAddSheaf X.toRingedSpace.sheaf)))
