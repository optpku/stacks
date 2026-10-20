/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.FunctionFieldDegree
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFunction
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.GenericallyFinite.Integral

/-!
# Generically finite morphisms and dimension functions

This file relates equality of relative dimensions to dominance and finiteness of the induced
extension of function fields.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A morphism between integral schemes of equal relative dimension over a universally
catenary base either has range in a proper closed subscheme or is dominant and induces a
finite extension of function fields. -/
theorem range_subset_properClosed_or_finiteFunctionFieldExtension
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [hXint : IsIntegral X.left] [hYint : IsIntegral Y.left] (f : X ⟶ Y)
    (hdim : X.hom.relativeDimensionFunction δ (genericPoint X.left) =
      Y.hom.relativeDimensionFunction δ (genericPoint Y.left)) :
    (∃ Z : Y.left.IdealSheafData,
      Z.support ≠ ⊤ ∧ Set.range f.left ⊆ (Z.support : Set Y.left)) ∨
      ∃ hdom : IsDominant f.left,
        @FiniteFunctionFieldExtension _ _ f.left hXint hYint hdom := sorry

end AlgebraicGeometry.Scheme.Hom
