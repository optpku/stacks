/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.BivariantClass.Smooth

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Proposition 42.60.2: composition with the smooth Gysin class identifies the
homogeneous bivariant groups with the relative-dimension degree shift. -/
@[stacks 0FBT] #check (AlgebraicGeometry.BivariantClass.compSmoothEquiv :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Y Z : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [LocallyOfFiniteType Z.hom] (f : X ⟶ Y) (g : Y ⟶ Z) [Smooth g.left] (d : ℕ)
    [Scheme.Hom.RelativeDimension g.left d] (p : ℤ),
    BivariantClass.group δ f p ≃+ BivariantClass.group δ (f ≫ g) (p - (d : ℤ)))
