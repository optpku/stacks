/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFunction.FlatCompatibility

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom.IsDimensionFunctionCompatible

/-- Compatibility with dimension functions composes for flat morphisms, with additive
shifts. -/
theorem comp {S S' S'' : Scheme.{u}}
    [UniversallyCatenary S] [UniversallyCatenary S'] [UniversallyCatenary S'']
    (g : S' ⟶ S) [Flat g] (g' : S'' ⟶ S') [Flat g']
    (δ : S → ℤ) [IsDimensionFunction δ] (δ' : S' → ℤ) [IsDimensionFunction δ']
    (δ'' : S'' → ℤ) [IsDimensionFunction δ''] (c c' : ℤ)
    (hcompat : g.IsDimensionFunctionCompatible δ δ' c)
    (hcompat' : g'.IsDimensionFunctionCompatible δ' δ'' c') :
    (g' ≫ g).IsDimensionFunctionCompatible δ δ'' (c + c') := sorry

end AlgebraicGeometry.Scheme.Hom.IsDimensionFunctionCompatible
