/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Functor.Const
public import ReasLib.Topology.Category.LCCat.Objects
public import ReasLib.Topology.Category.TopCat.DiagramOpens.Constant

/-!
# Underlying simplicial space of a simplicial LC object

A simplicial object of `LCCat` has an underlying simplicial space by whiskering with
`LCCat.toTopCat`. An augmentation in `LCCat` likewise forgets to an augmentation of
simplicial spaces, which is the input of `augmentationMorphism`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.SimplicialObject

universe u

namespace LCCat

/-- The underlying simplicial space of a simplicial object of `LCCat`. -/
abbrev forgetToTop : SimplicialObject LCCat.{u} ⥤ SimplicialObject TopCat.{u} :=
  (SimplicialObject.whiskering LCCat.{u} TopCat.{u}).obj toTopCat

/-- `forgetToTop` is postcomposition with `toTopCat`. -/
theorem forgetToTop_obj (U : SimplicialObject LCCat.{u}) :
    forgetToTop.obj U = U ⋙ toTopCat :=
  rfl

/-- The constant simplicial `LCCat` object forgets to the constant simplicial space on the
underlying topological space. -/
def forgetToTop_const (X : LCCat.{u}) :
    forgetToTop.obj ((SimplicialObject.const LCCat.{u}).obj X) ≅ constSpace X.obj :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro n m f
    change (𝟙 X.obj) ≫ 𝟙 X.obj = (𝟙 X.obj) ≫ 𝟙 X.obj
    rfl)

/-- Components of `forgetToTop_const` are identity morphisms. -/
theorem forgetToTop_const_app (X : LCCat.{u}) (n : SimplexCategoryᵒᵖ) :
    (forgetToTop_const X).app n = Iso.refl _ :=
  rfl

/-- The underlying augmentation of simplicial spaces associated to an augmentation in `LCCat`. -/
def toTopCatAugmentation {U : SimplicialObject LCCat.{u}} {X : LCCat.{u}}
    (a : U ⟶ (SimplicialObject.const LCCat.{u}).obj X) :
    forgetToTop.obj U ⟶ constSpace X.obj :=
  forgetToTop.map a ≫ (forgetToTop_const X).hom

/-- `toTopCatAugmentation` is `forgetToTop.map a` followed by `forgetToTop_const`. -/
theorem toTopCatAugmentation_def {U : SimplicialObject LCCat.{u}} {X : LCCat.{u}}
    (a : U ⟶ (SimplicialObject.const LCCat.{u}).obj X) :
    toTopCatAugmentation a = forgetToTop.map a ≫ (forgetToTop_const X).hom :=
  rfl

end LCCat
