/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.Additive
public import Mathlib.Algebra.Category.Grp.Basic

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

/-- The additive commutative group of homogeneous bivariant Chow classes of degree `p`. -/
def group
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) : AddCommGrpCat.{u + 1} where
  carrier := BivariantClass δ f p
  str := pointwiseAddCommGroup δ f p

end AlgebraicGeometry.BivariantClass
